
#include "PrecompiledHeader.h"

#ifdef WIN32
#include <windows.h>
#undef Yield
#endif

#include "AppCommon.h"
#include "App.h"

#include <cstdint>
#include <libretro.h>
#include <string>
#include <thread>
#include <wx/stdpaths.h>
#include <wx/dir.h>
#include <wx/evtloop.h>

#include "GS.h"
#include "options.h"
#include "input.h"
#include "svnrev.h"
#include "SPU2/Global.h"
#include "ps2/BiosTools.h"
#include "CDVD/CDVD.h"
#include "MTVU.h"

//#define PERF_TEST
#ifdef PERF_TEST
static struct retro_perf_callback perf_cb;

#define RETRO_PERFORMANCE_INIT(name)                 \
	retro_perf_tick_t current_ticks;                 \
	static struct retro_perf_counter name = {#name}; \
	if (!name.registered)                            \
		perf_cb.perf_register(&(name));              \
	current_ticks = name.total

#define RETRO_PERFORMANCE_START(name) perf_cb.perf_start(&(name))
#define RETRO_PERFORMANCE_STOP(name) \
	perf_cb.perf_stop(&(name));      \
	current_ticks = name.total - current_ticks;
#else
#define RETRO_PERFORMANCE_INIT(name)
#define RETRO_PERFORMANCE_START(name)
#define RETRO_PERFORMANCE_STOP(name)
#endif

namespace Options
{
static Option<std::string> bios("pcsx2_bios", "Bios"); // will be filled in retro_init()
static Option<bool> fast_boot("pcsx2_fastboot", "Fast Boot", true);

GfxOption<std::string> renderer("pcsx2_renderer", "Renderer", {"Auto",
#ifdef _WIN32
															   "D3D11",
#endif
															   "OpenGL", "Software", "Null"});

static GfxOption<bool> frameskip("pcsx2_frameskip", "Frameskip", false);
static GfxOption<int> frames_to_draw("pcsx2_frames_to_draw", "Frameskip: Frames to Draw", 1, 10);
static GfxOption<int> frames_to_skip("pcsx2_frames_to_skip", "Frameskip: Frames to Skip", 1, 10);
} // namespace Options

retro_environment_t environ_cb;
retro_video_refresh_t video_cb;
struct retro_hw_render_callback hw_render;
static ConsoleColors log_color = Color_Default;
static retro_log_printf_t log_cb;
static retro_audio_sample_batch_t batch_cb;
static retro_audio_sample_t sample_cb;

int Interpolation = 4;
bool EffectsDisabled = false;
bool postprocess_filter_dealias = false;
unsigned int delayCycles = 4;
static const int samples_max = 0x800;
static int write_pos = 0;
static s16 snd_buffer[samples_max << 1];
static Threading::Mutex snd_mutex;

// renderswitch - tells GSdx to go into dx9 sw if "renderswitch" is set.
bool renderswitch = false;
uint renderswitch_delay = 0;
static Pcsx2App* pcsx2;
static wxFileName bios_dir;

void retro_set_video_refresh(retro_video_refresh_t cb)
{
	video_cb = cb;
}

void retro_set_audio_sample_batch(retro_audio_sample_batch_t cb)
{
	batch_cb = cb;
}

void retro_set_audio_sample(retro_audio_sample_t cb)
{
	sample_cb = cb;
}

void SndBuffer::Write(const StereoOut32& Sample)
{
	ScopedLock locker(snd_mutex);
	if(write_pos < (samples_max << 1))
	{
		snd_buffer[write_pos++] = Sample.Left >> 12;
		snd_buffer[write_pos++] = Sample.Right >> 12;
	}
}

void retro_set_environment(retro_environment_t cb)
{
	environ_cb = cb;
	bool no_game = true;
	environ_cb(RETRO_ENVIRONMENT_SET_SUPPORT_NO_GAME, &no_game);
#ifdef PERF_TEST
	environ_cb(RETRO_ENVIRONMENT_GET_PERF_INTERFACE, &perf_cb);
#endif
}

static void RetroLog_DoSetColor(ConsoleColors color)
{
	if (color != Color_Current)
		log_color = color;
}

static void RetroLog_DoWrite(const wxString& fmt)
{
	retro_log_level level = RETRO_LOG_INFO;
	switch (log_color)
	{
		case Color_StrongRed: // intended for errors
			level = RETRO_LOG_ERROR;
			break;
		case Color_StrongOrange: // intended for warnings
			level = RETRO_LOG_WARN;
			break;
		case Color_Cyan:   // faint visibility, intended for logging PS2/IOP output
		case Color_Yellow: // faint visibility, intended for logging PS2/IOP output
		case Color_White:  // faint visibility, intended for logging PS2/IOP output
			level = RETRO_LOG_DEBUG;
			break;
		default:
		case Color_Default:
		case Color_Black:
		case Color_Green:
		case Color_Red:
		case Color_Blue:
		case Color_Magenta:
		case Color_Orange:
		case Color_Gray:
		case Color_StrongBlack:
		case Color_StrongGreen: // intended for infrequent state information
		case Color_StrongBlue:  // intended for block headings
		case Color_StrongMagenta:
		case Color_StrongGray:
		case Color_StrongCyan:
		case Color_StrongYellow:
		case Color_StrongWhite:
			break;
	}

	log_cb(level, "%s", (const char*)fmt);
}

static void RetroLog_SetTitle(const wxString& title)
{
	RetroLog_DoWrite(title + L"\n");
}

static void RetroLog_Newline()
{
	//	RetroLog_DoWrite(L"\n");
}

static void RetroLog_DoWriteLn(const wxString& fmt)
{
	RetroLog_DoWrite(fmt + L"\n");
}

static const IConsoleWriter ConsoleWriter_Libretro =
	{
		RetroLog_DoWrite,
		RetroLog_DoWriteLn,
		RetroLog_DoSetColor,

		RetroLog_DoWrite,
		RetroLog_Newline,
		RetroLog_SetTitle,

		0, // instance-level indentation (should always be 0)
};

static std::vector<const char*> disk_images;
static int image_index = 0;
static bool eject_state;
static bool RETRO_CALLCONV set_eject_state(bool ejected)
{
	if(eject_state == ejected)
		return false;

	eject_state = ejected;

	SetGSConfig().VsyncQueueSize = 100;
	GetMTGS().SignalVsync();
	CoreThread.Pause();
	SetGSConfig().VsyncQueueSize = 2;

	if(ejected)
		cdvdCtrlTrayOpen();
	else
	{
		if(image_index < 0 || image_index >= (int)disk_images.size())
			g_Conf->CdvdSource = CDVD_SourceType::NoDisc;
		else
		{
			g_Conf->CurrentIso = disk_images[image_index];
			g_Conf->CdvdSource = CDVD_SourceType::Iso;
			CDVDsys_SetFile(CDVD_SourceType::Iso, g_Conf->CurrentIso);
		}
		cdvdCtrlTrayClose();
	}

	CoreThread.Resume();
	return true;
}
static bool RETRO_CALLCONV get_eject_state(void)
{	
	return eject_state;
}

static unsigned RETRO_CALLCONV get_image_index(void)
{
	return image_index;
}
static bool RETRO_CALLCONV set_image_index(unsigned index)
{
	if(eject_state)
		image_index = index;

	return eject_state;
}
static unsigned RETRO_CALLCONV get_num_images(void)
{
	return disk_images.size();
}

static bool RETRO_CALLCONV replace_image_index(unsigned index, const struct retro_game_info* info)
{
	if (index >= disk_images.size())
		return false;

	if(!info->path)
	{
		disk_images.erase(disk_images.begin() + index);
		if (!disk_images.size())
			image_index = -1;
		else if (image_index > (int)index)
			image_index--;
	}
	else
		disk_images[index] = info->path;

	return true;
}

static bool RETRO_CALLCONV add_image_index(void)
{
	disk_images.push_back(nullptr);
	return true;
}

static bool RETRO_CALLCONV set_initial_image(unsigned index, const char* path)
{
	if (index >= disk_images.size())
		index = 0;

	image_index = index;

	return true;
}

static bool RETRO_CALLCONV get_image_path(unsigned index, char* path, size_t len)
{
	if (index >= disk_images.size())
		return false;

	if (!disk_images[index])
		return false;

	strncpy(path, disk_images[index], len);
	return true;
}
static bool RETRO_CALLCONV get_image_label(unsigned index, char* label, size_t len)
{
	if (index >= disk_images.size())
		return false;

	if (!disk_images[index])
		return false;

	strncpy(label, disk_images[index], len);
	return true;
}

void retro_init(void)
{
	enum retro_pixel_format xrgb888 = RETRO_PIXEL_FORMAT_XRGB8888;
	environ_cb(RETRO_ENVIRONMENT_SET_PIXEL_FORMAT, &xrgb888);
	struct retro_log_callback log;
	if (environ_cb(RETRO_ENVIRONMENT_GET_LOG_INTERFACE, &log))
	{
		log_cb = log.log;
#if 0
		Console_SetActiveHandler(ConsoleWriter_Libretro);
#endif
	}

	//	pcsx2 = new Pcsx2App;
	//	wxApp::SetInstance(pcsx2);
	pcsx2 = &wxGetApp();
#if 0
	int argc = 0;
	pcsx2->Initialize(argc, (wchar_t**)nullptr);
	wxModule::RegisterModules();
	wxModule::InitializeModules();
#endif

	InitCPUTicks();
	//	pxDoAssert = AppDoAssert;
	pxDoAssert = NULL;
	pxDoOutOfMemory = SysOutOfMemory_EmergencyResponse;
	g_Conf = std::make_unique<AppConfig>();
	i18n_SetLanguage(wxLANGUAGE_DEFAULT);
	i18n_SetLanguagePath();
	GetSysExecutorThread().Start();
	pcsx2->DetectCpuAndUserMode();
	pcsx2->AllocateCoreStuffs();
	//	pcsx2->GetGameDatabase();
	vu1Thread.Reset();

	g_Conf->BaseFilenames.Plugins[PluginId_GS] = "Built-in";
	g_Conf->BaseFilenames.Plugins[PluginId_PAD] = "Built-in";
	g_Conf->BaseFilenames.Plugins[PluginId_USB] = "Built-in";
	g_Conf->BaseFilenames.Plugins[PluginId_DEV9] = "Built-in";

	if (Options::bios.empty())
	{
		const char* system = nullptr;
		environ_cb(RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY, &system);
		bios_dir = Path::Combine(system, "pcsx2/bios");

		wxArrayString bios_list;
		wxDir::GetAllFiles(bios_dir.GetFullPath(), &bios_list, L"*.*", wxDIR_FILES);

		for (wxString bios_file : bios_list)
		{
			wxString description;
			if (IsBIOS(bios_file, description))
				Options::bios.push_back((const char*)description, (const char*)bios_file);
		}
	}

	Options::SetVariables();

	static retro_disk_control_ext_callback disk_control = {
		set_eject_state,
		get_eject_state,
		get_image_index,
		set_image_index,
		get_num_images,
		replace_image_index,
		add_image_index,
		set_initial_image,
		get_image_path,
		get_image_label,
	};

	environ_cb(RETRO_ENVIRONMENT_SET_DISK_CONTROL_EXT_INTERFACE, &disk_control);
}

void retro_deinit(void)
{
	//	GetCoreThread().Cancel(true);

	// WIN32 doesn't allow canceling threads from global constructors/destructors in a shared library.
	vu1Thread.Cancel();
	pcsx2->CleanupOnExit();
#ifdef PERF_TEST
	perf_cb.perf_log();
#endif
}

void retro_get_system_info(retro_system_info* info)
{
#ifdef GIT_REV
	info->library_version = GIT_REV;
#else
	static char version[] = "#.#.#";
	version[0] = '0' + PCSX2_VersionHi;
	version[2] = '0' + PCSX2_VersionMid;
	version[4] = '0' + PCSX2_VersionLo;
	info->library_version = version;
#endif

	info->library_name = "pcsx2";
	info->valid_extensions = "elf|iso|ciso|cue|bin";
	info->need_fullpath = true;
	info->block_extract = true;
}

void retro_get_system_av_info(retro_system_av_info* info)
{
	if (Options::renderer == "Software" || Options::renderer == "Null")
	{
		info->geometry.base_width = 640;
		info->geometry.base_height = 448;
	}
	else
	{
		info->geometry.base_width = 640 * Options::upscale_multiplier;
		info->geometry.base_height = 448 * Options::upscale_multiplier;
	}

	info->geometry.max_width = info->geometry.base_width;
	info->geometry.max_height = info->geometry.base_height;

	info->geometry.aspect_ratio = 4.0f / 3.0f;
	info->timing.fps = (retro_get_region() == RETRO_REGION_NTSC) ? (60.0f / 1.001f) : 50.0f;
	info->timing.sample_rate = 48000;
}

void retro_reset(void)
{
	GetMTGS().ClosePlugin();
	GetCoreThread().ResetQuick();
	GetMTGS().OpenPlugin();
	GetCoreThread().Resume();
	eject_state = false;
	write_pos = 0;
}

static void context_reset()
{
	printf("Context reset\n");
	GetMTGS().OpenPlugin();
	GetCoreThread().Resume();
	//	GSsetVsync(0);
}
static void context_destroy()
{
	//	GetCoreThread().Pause();
	SetGSConfig().VsyncQueueSize = 100;
	GetMTGS().ClosePlugin();
	GetCoreThread().Pause();
	SetGSConfig().VsyncQueueSize = 2;
//	GetCoreThread().Suspend();

	printf("Context destroy\n");
}

static bool set_hw_render(retro_hw_context_type type)
{
	hw_render.context_type = type;
	hw_render.context_reset = context_reset;
	hw_render.context_destroy = context_destroy;
	hw_render.bottom_left_origin = true;
	hw_render.depth = true;
	hw_render.cache_context = true;

	switch (type)
	{
		case RETRO_HW_CONTEXT_DIRECT3D:
			hw_render.version_major = 11;
			hw_render.version_minor = 0;
			break;

		case RETRO_HW_CONTEXT_OPENGL_CORE:
			hw_render.version_major = 3;
			hw_render.version_minor = 3;
			hw_render.cache_context = false;
			break;

		case RETRO_HW_CONTEXT_OPENGL:
			hw_render.version_major = 3;
			hw_render.version_minor = 0;
			break;

		case RETRO_HW_CONTEXT_OPENGLES3:
			hw_render.version_major = 3;
			hw_render.version_minor = 0;
			break;

		case RETRO_HW_CONTEXT_NONE:
			return true;

		default:
			return false;
	}

	return environ_cb(RETRO_ENVIRONMENT_SET_HW_RENDER, &hw_render);
}

bool retro_load_game(const struct retro_game_info* game)
{
	if (Options::bios.empty())
	{
		log_cb(RETRO_LOG_ERROR, "Could not find any valid PS2 Bios File in %s\n", (const char*)bios_dir.GetFullPath());
		return false;
	}

	const char* system = nullptr;
	environ_cb(RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY, &system);

	//	pcsx2->Overrides.Gamefixes.Set( id, true);

	// By default no IRX injection
	g_Conf->CurrentIRX = "";
	g_Conf->BaseFilenames.Bios = Options::bios.Get();
	eject_state = false;
	write_pos = 0;

	Options::renderer.UpdateAndLock(); // disallow changes to Options::renderer outside of retro_load_game.

	u32 magic = 0;
	if (game)
	{
		FILE* fp = fopen(game->path, "rb");
		if (!fp)
		{
			log_cb(RETRO_LOG_ERROR, "Could not open File: %s\n", game->path);
			return false;
		}

		fread(&magic, 4, 1, fp);
		fclose(fp);
	}

	if (magic == 0x464C457F) // elf
	{
		// g_Conf->CurrentIRX = "";
		g_Conf->EmuOptions.UseBOOT2Injection = true;
		pcsx2->SysExecute(CDVD_SourceType::NoDisc, game->path);
	}
	else
	{
		g_Conf->EmuOptions.UseBOOT2Injection = Options::fast_boot;
		g_Conf->CdvdSource = game ? CDVD_SourceType::Iso : CDVD_SourceType::NoDisc;
		g_Conf->CurrentIso = game ? game->path : "";
		pcsx2->SysExecute(g_Conf->CdvdSource);
	}

	//	g_Conf->CurrentGameArgs = "";
	g_Conf->EmuOptions.GS.FrameLimitEnable = false;
	//	g_Conf->EmuOptions.GS.SynchronousMTGS = true;

	Input::Init();

	if (Options::renderer == "Auto")
	{
		retro_hw_context_type context_type = RETRO_HW_CONTEXT_OPENGL_CORE;
		environ_cb(RETRO_ENVIRONMENT_GET_PREFERRED_HW_RENDER, &context_type);
		return set_hw_render(context_type);
	}
#ifdef _WIN32	
	if (Options::renderer == "D3D11")
		return set_hw_render(RETRO_HW_CONTEXT_DIRECT3D);
#endif
	if (Options::renderer == "Null")
		return set_hw_render(RETRO_HW_CONTEXT_NONE);

	if (set_hw_render(RETRO_HW_CONTEXT_OPENGL_CORE))
		return true;
	if (set_hw_render(RETRO_HW_CONTEXT_OPENGL))
		return true;
	if (set_hw_render(RETRO_HW_CONTEXT_OPENGLES3))
		return true;

	return false;
}

bool retro_load_game_special(unsigned game_type, const struct retro_game_info* info,
							 size_t num_info)
{
	return false;
}

void retro_unload_game(void)
{	
	SetGSConfig().VsyncQueueSize = 100;
//	GetMTGS().Flush();
	GetMTGS().ClosePlugin();
	GetCoreThread().Suspend();
	SetGSConfig().VsyncQueueSize = 2;
}


void retro_run(void)
{
	Options::CheckVariables();
	SetGSConfig().FrameSkipEnable = Options::frameskip;
	SetGSConfig().FramesToDraw = Options::frames_to_draw;
	SetGSConfig().FramesToSkip = Options::frames_to_skip;

	Input::Update();

	if (Options::upscale_multiplier.Updated())
	{
		retro_system_av_info av_info;
		retro_get_system_av_info(&av_info);
#if 1
		environ_cb(RETRO_ENVIRONMENT_SET_SYSTEM_AV_INFO, &av_info);
#else
		environ_cb(RETRO_ENVIRONMENT_SET_GEOMETRY, &av_info.geometry);
		GetMTGS().ClosePlugin();
		GetMTGS().OpenPlugin();
#endif
	}

	//	GetCoreThread().Resume();
	GetMTGS().OpenPlugin();

	RETRO_PERFORMANCE_INIT(pcsx2_run);
	RETRO_PERFORMANCE_START(pcsx2_run);

	GetMTGS().StepFrame();

	if (write_pos > (0x200 << 1))
	{
		ScopedLock locker(snd_mutex);
		batch_cb(snd_buffer, write_pos >> 1);
		write_pos = 0;
	}

	RETRO_PERFORMANCE_STOP(pcsx2_run);
}

size_t retro_serialize_size(void)
{
	return Ps2MemSize::MainRam + Ps2MemSize::Scratch + Ps2MemSize::Hardware +
			Ps2MemSize::IopRam + Ps2MemSize::IopHardware +
			VU0_PROGSIZE + VU0_MEMSIZE + VU1_PROGSIZE + VU1_MEMSIZE +
			_8mb;// + SPU2Savestate::SizeIt();
}

bool retro_serialize(void* data, size_t size)
{
	SetGSConfig().VsyncQueueSize = 100;
	GetMTGS().SignalVsync();
	CoreThread.Pause();
	SetGSConfig().VsyncQueueSize = 2;
	GetMTGS().Flush();

	VmStateBuffer buffer;
	memSavingState saveme(buffer);

	saveme.FreezeAll();

	memcpy(data, buffer.GetPtr(), buffer.GetLength());
	SPU2Savestate::FreezeIt(*(SPU2Savestate::DataBlock*)((u8*)data + buffer.GetLength()));

	CoreThread.Resume();
	return true;
}

bool retro_unserialize(const void* data, size_t size)
{
	SetGSConfig().VsyncQueueSize = 100;
	GetMTGS().SignalVsync();
	CoreThread.Pause();
	SetGSConfig().VsyncQueueSize = 2;
	GetMTGS().Flush();

	VmStateBuffer buffer;
	buffer.MakeRoomFor(size);
	memcpy(buffer.GetPtr(), data, size);

	memLoadingState loadme(buffer);

	loadme.FreezeAll();
	SPU2Savestate::ThawIt(*(SPU2Savestate::DataBlock*)loadme.GetBlockPtr());

	CoreThread.Resume();
	return true;
}

unsigned retro_get_region(void)
{
	return RETRO_REGION_NTSC;
}

unsigned retro_api_version()
{
	return RETRO_API_VERSION;
}

size_t retro_get_memory_size(unsigned id)
{
	return 0;
}

void* retro_get_memory_data(unsigned id)
{
	return NULL;
}

void retro_cheat_reset(void)
{
}

void retro_cheat_set(unsigned index, bool enabled, const char* code)
{
}

void SndBuffer::Init()
{
	write_pos = 0;
}

void SndBuffer::Cleanup()
{
}

s32 SndBuffer::Test()
{
	return 0;
}

void SndBuffer::ClearContents()
{
}

void DspUpdate()
{
}

s32 DspLoadLibrary(wchar_t* fileName, int modnum)
{
	return 0;
}

void ReadSettings()
{
}
#ifndef _WIN32
void SysMessage(const char* fmt, ...)
{
	va_list list;
	va_start(list, fmt);
	vprintf(fmt, list);
	va_end(list);
}
#endif
wxEventLoopBase* Pcsx2AppTraits::CreateEventLoop()
{
	return new wxEventLoop();
	//	 return new wxGUIEventLoop();
	//	 return new wxConsoleEventLoop();
}

#ifdef wxUSE_STDPATHS
class Pcsx2StandardPaths : public wxStandardPaths
{
public:
	virtual wxString GetExecutablePath() const
	{
		const char* system = nullptr;
		environ_cb(RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY, &system);
		return Path::Combine(system, "pcsx2/PCSX2");
	}
	wxString GetResourcesDir() const
	{
		const char* system = nullptr;
		environ_cb(RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY, &system);
		return Path::Combine(system, "pcsx2/Langs");
	}
	wxString GetUserLocalDataDir() const
	{
		const char* savedir = nullptr;
		environ_cb(RETRO_ENVIRONMENT_GET_SAVE_DIRECTORY, &savedir);
		return Path::Combine(savedir, "pcsx2");
	}
};

wxStandardPaths& Pcsx2AppTraits::GetStandardPaths()
{
	static Pcsx2StandardPaths stdPaths;
	return stdPaths;
}
#endif
