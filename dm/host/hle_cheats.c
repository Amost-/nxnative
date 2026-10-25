// Atmosphère-format cheat codes (the dmnt cheat VM) applied to the running game: the `.txt` files that cheat sites share as
// atmosphere/contents/<title ID>/cheats/<build ID>.txt, loaded by the first 16 hex digits (8 bytes) of the main NSO's
// build ID (dm_main_build(), from the rewriter's fixups header). The Mac front end shows them in the window's Cheats menu
// (front_mac.m); toggles are remembered per build in <build>.enabled in the cheats folder and restored at the next launch.
// The host applies the enabled cheats once per presented frame (hle_nvn.c dump_frame -> dm_cheats_present) and at a fixed
// ~60 Hz from its own thread when the game is not presenting (window minimized, graphics suspended, start-up).
// The cheat VM follows the reference implementation (Atmosphère stratosphere/dmnt/source/cheat/impl/dmnt_cheat_vm.cpp and
// docs/features/cheats.md) in word order, conditions, loops (jump-back counters) and register semantics; one deliberate
// difference: each cheat runs as its own program per pass (the reference concatenates them into one), so an unclosed
// conditional in one cheat cannot swallow the next cheat's words. Implemented opcodes: 0 store static, 1 begin
// conditional, 2 end / else, 3 loop, 4 load register static, 5 load register from memory, 6 store static to a register
// address, 7 legacy arithmetic, 8 key-press conditional. A cheat that uses anything else (register arithmetic 9, store
// register A / B, the C0..C3 conditional forms, pause / resume, the debug log, or an unknown form) is turned off before
// it ever runs, shown in the menu with "(unsupported opcode N)"; only the reference's memory regions 0 (main NSO) and
// 1 (heap) are mapped here. Every access is bounds-checked against the mapped main span and the opened heap: an
// out-of-range access turns the cheat off and logs a [RED] line, and the game keeps running.
// Switches of this file:
//   DM_CHEATS=<folder>      cheats folder (default <DM_ROOT>/cheats; the flat layout with the Atmosphère tree under it)
//   DM_CHEATS_ANY_BUILD=1   with no file of this build, load the folder's single .txt of another build, with a warning
//   DM_CHEATS_ON=<n>,…      cheats turned on by name at launch (the menu's own toggle states stay what they were)
//   DM_CHEATS_DEBUG=1       log every applied write (cheat name, where, value)
#include "dm.h"
#include "dm_input.h"   // dm_cheats_keys, the key mask the type-8 conditional reads
#include <libkern/OSCacheControl.h>
#include <sys/mman.h>
#if !TARGET_OS_IPHONE
#include <mach/mach.h>       // the alias mapping of main's pages (mach_vm_remap), below
#include <mach/mach_vm.h>
#include <mach/vm_prot.h>
#endif
#include <errno.h>
#include <dirent.h>
#include <unistd.h>
#include <strings.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <ctype.h>

// Limits of Atmosphère's own order (0x2000 dwords of program, 256 cheats per file): no shared cheat-site file and no
// hand-made one can exhaust the arrays
#define CHEAT_MAX 256          // cheats in one file
#define INS_MAX  0x2000        // dwords of one cheat's program
#define NAME_MAX 128           // characters of a [Name] / {Name} header
#define OTHER_MAX 24           // another build's .txt files listed in the menu
#define CAND_MAX 64            // .txt files scanned in the cheats folder and its Atmosphère tree
#define VM_STEP_CAP 4000000    // instructions of one cheat in one pass (the reference has none; a runaway loop must never stall a frame)

typedef struct {
    char name[NAME_MAX];       // the [Name] / {Name} header line, trimmed
    uint32_t ins[INS_MAX];     // the cheat's code words, one program run per pass
    int nins;
    uint8_t master;            // {Name} header: always on, applied first, not toggleable from the menu
    uint8_t on;                // switched on (masters always; everyone else by the menu's saved <build>.enabled state)
    uint8_t broken;            // unsupported opcode / region / width / condition, or malformed: shown disabled, never runs
    uint8_t dead;              // an out-of-range access at run time turned it off (until the next reload of the file)
    char why[80];              // the disabled state the menu shows (with the reason), filled at load or at run time
} cheat_t;

static cheat_t g_cheat[CHEAT_MAX]; static int g_ncheat;
static char g_dir[1024];       // cheats folder (DM_CHEATS or <DM_ROOT>/cheats), "" when neither is set
static char g_path[2048];      // the loaded file (logged; "Reload cheats" re-reads exactly this path)
static char g_build[17];       // the loaded file's build ID: main's build ID cut to 16 hex digits, upper case as the
                               // cheat files name it (dmnt matches the file name case-insensitively on disk)
static char g_tid[17];         // this game's title ID (the profile's DM_GAME_PROGRAM_ID), for the Atmosphère tree
static char g_others[OTHER_MAX][17]; static int g_nothers;   // builds on disk that are not this game's build
static char g_on[16][NAME_MAX]; static int g_non;            // the names of DM_CHEATS_ON, turned on at load time
static _Atomic int g_active;   // a file is loaded (the per-present hook exits before taking any lock)
static _Atomic uint64_t g_present_ns;   // the last present: the ~60 Hz thread stands down while it is recent
static _Atomic int g_dbg;      // DM_CHEATS_DEBUG
static int g_any;              // DM_CHEATS_ANY_BUILD
static _Atomic int g_inited;   // dm_cheats_init done (the thread keeps running under the consoleless iOS app too)

// Region 0: the guest main NSO as the loader mapped it (dm/host/loader.c map_image: text pages and the patch area
// read+execute, data and bss read+write, the host's key page read-only at the image's end); region 1: the heap,
// whose opened extent grows and shrinks as the game's heap does (hle_svc.c)
static module_t *g_main_mod;   // the "main" module of the profile (not an NRO), found at init; its loaded fields come from loader.c

// A second mapping of main's memory (same physical pages, mach_vm_remap with copy = false), protected read+write for the
// whole process: a cheat's write to a code page goes through it while the game's own mapping stays executable. Toggling
// the original page mprotect RW -> copy -> RX on every write races with the game's running cores: between the first
// mprotect and the restore their fetches of any instruction on that page fault (a 16 KB macOS page holds ~4 KB of
// instructions, found when main+0x305DD98 faulted while the poke page 0x305F3FC was toggled, run xa). With the alias the
// protections never change, so only the honest mid-word race the reference on Switch itself has is left. NULL when the
// remap failed: writes fall back to the per-page mprotect toggle (kept below), logged [RED] once
static uint8_t *g_alias;       // the alias mapping of main's image (same layout, page rounded up); every offset a
                               // cheat reaches is bounds-checked against main's own span first, so the page-rounded
                               // size needs no variable of its own
static int g_alias_fallback;   // the fallback [RED] was already logged once

// Map main's image a second time, writable. Called once a cheat file is actually picked (at init that is before the
// guest starts, so nothing protects or tracks these pages yet); the mapping stays for the process's lifetime, the
// loader's per-page protections never change after load. iPhone only: its SDK forbids mach_vm.h, and there the
// guarded main_write_pages falls back to the per-page mprotect toggle (unsampled, plain C must stay compiling)
#if TARGET_OS_IPHONE
static void alias_setup(void) { g_alias = NULL; }
#else
static void alias_setup(void) {
    module_t *m = g_main_mod;
    long pg = sysconf(_SC_PAGESIZE); if (pg <= 0) pg = 0x4000;   // 16 KB on Apple Silicon, a safe floor elsewhere
    uint64_t size = ((uint64_t)m->size + (uint64_t)pg - 1) & ~((uint64_t)pg - 1);   // mach_vm_remap wants whole pages
    mach_vm_address_t dst = 0;
    vm_prot_t cur = 0, mx = 0;
    kern_return_t kr = mach_vm_remap(mach_task_self(), &dst, size, 0, VM_FLAGS_ANYWHERE,
                                     mach_task_self(), (mach_vm_address_t)(uintptr_t)m->base, FALSE,
                                     &cur, &mx, VM_INHERIT_SHARE);
    if (kr) { g_alias = NULL; return; }
    // The alias's protections are independent of the original mapping's: make everything writable once. The key page
    // stays refused by the write path; the alias is only ever used by a check-passing write
    kr = mach_vm_protect(mach_task_self(), dst, size, 0, VM_PROT_READ | VM_PROT_WRITE);
    if (kr) { mach_vm_deallocate(mach_task_self(), dst, size); g_alias = NULL; return; }
    g_alias = (uint8_t *)(uintptr_t)dst;
}
#endif

// The cheats list, the toggles and one VM pass at a time
static pthread_mutex_t g_lock = PTHREAD_MUTEX_INITIALIZER;

// A cheat turned itself off for good (until the file is reloaded): the menu shows it disabled with the reason
static void cheat_kill(cheat_t *c, const char *fmt, ...) {
    if (c->dead) return;
    c->dead = 1;
    va_list ap; va_start(ap, fmt);
    char msg[160]; vsnprintf(msg, sizeof msg, fmt, ap);
    va_end(ap);
    snprintf(c->why, sizeof c->why, " (off: %s)", msg);
    LOG("[RED] cheat \"%s\": %s, turning it off", c->name, msg);
}

// ---------- decode: one decoder for both the load verdict and the run ----------

// The Atmosphère opcode of the instruction starting at *p: a nibble, extended by the second and third nibble for the
// 0xC / 0xF forms (register conditionals; pause / resume / debug log), the way the reference DecodeNextOpcode does it
static unsigned op_kind(uint32_t w) {
    unsigned op = w >> 28;
    if (op >= 0xC) op = (op << 4) | ((w >> 24) & 0xF);
    if (op >= 0xF0) op = (op << 4) | ((w >> 20) & 0xF);
    return op;
}

// Conditional begins (1 / 8 / C4): when a failed conditional is skipped, its whole nested block must be walked to its
// own end / else, so each of these increases the depth counter
static int op_cond_begin(unsigned op) { return op == 1 || op == 8 || op == 0xC4; }

// Unsupported opcode, with the reference's own opcode name in the menu label ("unsupported opcode A", "… FF0")
static int ins_unsupported(cheat_t *c, const uint32_t *p) {
    snprintf(c->why, sizeof c->why, " (unsupported opcode %X)", op_kind(p[0]));
    c->broken = 1;
    return 0;
}

// One unsupported verdict, of the reasons the reference can still decode but the host does not run
#define UNSUP(c, what) { snprintf((c)->why, sizeof (c)->why, " (%s)", what); (c)->broken = 1; return 0; }

// The instruction the way the run and the load verdict must both see it: fields from the reference's decode, one place.
// rel = the 40-bit relative address, val = the static value / a loop's iterations / the key mask
typedef struct {
    unsigned op, len, t, m, r, x, c, flags;
    uint64_t rel, val;
} ins_t;

// Decode the instruction at p (n words left) or 0 when it cannot run here (c->why: why). Mirrors the reference
// DecodeNextOpcode field by field, so the run never miscounts a word; outside what the host implements
// (opcodes 0,1,2,3,4,5,6,7,8 with the reference's value widths and its six comparisons) the verdict is unsupported
static int ins_dec(cheat_t *c, const uint32_t *p, int n, ins_t *o) {
    unsigned t;
    if (n <= 0) UNSUP(c, "truncated");
    memset(o, 0, sizeof *o);
    uint32_t w = p[0];
    o->op = op_kind(w); o->len = 1;
    switch (o->op) {
        case 0: {   // 0TMR00AA AAAAAAAA VVVVVVVV (VVVVVVVV): store the value at memory base + rel + reg[r]
                    // (the reference adds the offset register unconditionally: all registers start at 0)
            if ((t = (w >> 24) & 0xF, t != 1 && t != 2 && t != 4 && t != 8)) UNSUP(c, "width");
            if ((o->m = (w >> 20) & 0xF) > 1) UNSUP(c, "region");
            o->t = t; o->r = (w >> 16) & 0xF;
            if (n < 2) UNSUP(c, "truncated");
            o->rel = ((uint64_t)(w & 0xFF) << 32) | p[1];
            o->len = 3;
            if (o->t == 8) {   // a width-8 value comes in the reference's word order: first dword high, second low
                if (n < 4) UNSUP(c, "truncated");
                o->val = ((uint64_t)p[2] << 32) | p[3]; o->len = 4;
            } else o->val = p[2];
        } break;
        case 1: {   // 1TMCXrAA AAAAAAAA VVVVVVVV (VVVVVVVV): compare memory at base + rel (+ reg[x] for X=1) with the value
            if ((t = (w >> 24) & 0xF, t != 1 && t != 2 && t != 4 && t != 8)) UNSUP(c, "width");
            if ((o->m = (w >> 20) & 0xF) > 1) UNSUP(c, "region");
            o->t = t; o->c = (w >> 16) & 0xF;
            if (o->c < 1 || o->c > 6) UNSUP(c, "condition");   // only the six comparisons run
            o->flags = ((w >> 12) & 0xF) != 0;                 // X, taken as a boolean like the reference does
            o->x = (w >> 8) & 0xF;
            if (n < 2) UNSUP(c, "truncated");
            o->rel = ((uint64_t)(w & 0xFF) << 32) | p[1];
            o->len = 3;
            if (o->t == 8) {
                if (n < 4) UNSUP(c, "truncated");
                o->val = ((uint64_t)p[2] << 32) | p[3]; o->len = 4;
            } else o->val = p[2];
        } break;
        case 2:     // 2X000000: end of a conditional, else for X = 1 (the reference reads it as an else flag)
            o->flags = ((w >> 24) & 0xF) == 1;
            break;
        case 3: {   // 300R0000 VVVVVVVV starts (the reference's Loop, reg r counted), 310R0000 ends (the same r again;
                    // any X but 0 at nibble 1 is the end form, the way DecodeNextOpcode reads start_loop == 0)
            o->flags = ((w >> 24) & 0xF) != 0;
            o->r = (w >> 16) & 0xF;
            if (!o->flags) {
                if (n < 2) UNSUP(c, "truncated");
                o->val = p[1]; o->len = 2;
            }
        } break;
        case 4: {   // 400R0000 VVVVVVVV VVVVVVVV: reg[r] = the 64-bit value
            if (n < 3) UNSUP(c, "truncated");
            o->r = (w >> 16) & 0xF;
            o->val = ((uint64_t)p[1] << 32) | p[2]; o->len = 3;
        } break;
        case 5: {   // 5TMR00AA / 5T0R10AA / 5T0R2SAA / 5TMR3SAA AAAAAAAA: reg[r] = the width bytes of one address
            if ((t = (w >> 24) & 0xF, t != 1 && t != 2 && t != 4 && t != 8)) UNSUP(c, "width");
            o->t = t; o->m = (w >> 20) & 0xF; o->r = (w >> 16) & 0xF;
            o->flags = (w >> 12) & 0xF; o->x = (w >> 8) & 0xF;   // flags: 0 fixed, 1 reg[r] + rel, 2 reg[x] + rel, 3 region + reg[x] + rel
            if (o->flags > 3) UNSUP(c, "operand");
            if ((o->flags == 0 || o->flags == 3) && o->m > 1) UNSUP(c, "region");
            if (n < 2) UNSUP(c, "truncated");
            o->rel = ((uint64_t)(w & 0xFF) << 32) | p[1]; o->len = 2;
        } break;
        case 6: {   // 6T0RIor0 VVVVVVVV VVVVVVVV: the value at reg[r] (+ reg[x] for o=1), reg[r] + width for I=1
            if ((t = (w >> 24) & 0xF, t != 1 && t != 2 && t != 4 && t != 8)) UNSUP(c, "width");
            if (n < 3) UNSUP(c, "truncated");
            o->t = t; o->r = (w >> 16) & 0xF;
            o->flags = (((w >> 12) & 0xF) != 0) | (((w >> 8) & 0xF) != 0) << 1;   // 1 = increment reg[r], 2 = add reg[x]
            o->x = (w >> 4) & 0xF;
            o->val = ((uint64_t)p[1] << 32) | p[2]; o->len = 3;
        } break;
        case 7: {   // 7T0RC000 VVVVVVVV: reg[r] performs the width arithmetic with the value
            if ((t = (w >> 24) & 0xF, t != 1 && t != 2 && t != 4 && t != 8)) UNSUP(c, "width");
            if ((o->c = (w >> 12) & 0xF) > 4) UNSUP(c, "arithmetic");   // the five legacy operations
            o->t = t; o->r = (w >> 16) & 0xF;
            if (n < 2) UNSUP(c, "truncated");
            o->val = p[1]; o->len = 2;
        } break;
        case 8:     // 8kkkkkkk: every key of the mask held; the DM_BTN_* bit order, the sticks' directions on 16..23
                    // (dm_input.h); SL / SR on 24 / 25 can never be held, no input source of this host reports them
            o->val = w & 0x0FFFFFFFu;
            break;
        default:    // 9, A, B, C0... and any unknown form
            return ins_unsupported(c, p);
    }
    if (o->len > (unsigned)n) UNSUP(c, "truncated");   // the cheat's words end in the middle of an instruction
    return (int)o->len;
}

// ---------- guest memory: the spans a cheat may touch, and the accesses into them ----------

// The span that contains the host pointer range [addr, addr+len). kind 0 = main's mapped image, kind 1 = the currently
// opened heap; NULL when any byte of the range is unmapped (rel_base is optional: callers that log only the raw guest
// address pass NULL)
static uint8_t *span_get(uint64_t addr, uint64_t len, int *kind, uint64_t *rel_base) {
    if (g_main_mod) {
        uint64_t b = (uint64_t)(uintptr_t)g_main_mod->base, off = addr - b;
        if (addr >= b && off < g_main_mod->size && len <= g_main_mod->size - off) {
            *kind = 0; if (rel_base) *rel_base = b; return (uint8_t *)(uintptr_t)addr;
        }
    }
    uint64_t hb; size_t hopen; dm_guest_heap_range(&hb, &hopen);
    if (hb && hopen && addr >= hb && addr - hb < hopen && len <= hopen - (addr - hb)) {
        *kind = 1; if (rel_base) *rel_base = hb; return (uint8_t *)(uintptr_t)addr;
    }
    return NULL;
}

// Cheats writing into main's pages (dmnt's WriteCheatProcessMemoryUnsafe on this host): if the writable alias of main
// was mapped at init (alias_setup), everything is copied through it — the same physical memory, the game's own mapping
// stays untouched and executable, no mprotect at write time. Without the alias (a remap failure) the code pages (text
// to its text_end, the patch area) are toggled writable, copied and put back per page, and the instruction cache is
// invalidated, so the game's fetches see exactly what the cheat says (the rewriter may have rewritten the same
// instruction; the cheat still overwrites it when enabled) — but that path races with the game's running cores (see
// alias_setup), so it logs a [RED] once and is truly a last resort. The key page (this host's TLS slot numbers, inside
// the mapped image) is refused either way: changing it would break every guest thread
static int main_write_pages(cheat_t *c, uint64_t addr, uint64_t len, const void *src) {
    static long pg; if (!pg) pg = getpagesize();
    module_t *m = g_main_mod; uint64_t mb = (uint64_t)(uintptr_t)m->base;
    uint64_t rx_end = (m->text_end + pg - 1) & ~(uint64_t)(pg - 1);                    // the text as mprotect'd at load
    // The patch area when it follows the image (patch_off >= 0), page-rounded. When it lies before the base
    // (patch_off < 0, the loader's large-image layout) m->size excludes it and no cheat write can reach it: po = size
    // leaves the second code range below empty. UINT64_MAX there would wrap mb + po to mb - 1, make every page count
    // as code in the fallback (a [mb - 1, ...) test) and seal data / bss pages R|X, which faults the game's next write
    uint64_t po = m->patch_off >= 0 ? ((uint64_t)m->patch_off & ~(uint64_t)(pg - 1)) : (uint64_t)m->size;
    uint64_t kp0 = mb + m->key_page_off, kp1 = kp0 + m->key_page_size;
    if (addr < kp1 && addr + len > kp0) {   // the write would cover the key page: refuse it like an out-of-range access
        cheat_kill(c, "write into the host key page is refused");
        return -1;
    }
    dm_guest_write_prepare((void *)(uintptr_t)addr, len);   // the write-protect dirty tracking must see this write coming
    const uint8_t *v = src;
    uint64_t start = addr;                  // kept for the icache invalidate: the fallback loop walks addr past it
    if (g_alias) {
        memcpy(g_alias + (size_t)(addr - mb), v, len);   // through the writable alias, the same image offset
    } else {
        if (!g_alias_fallback) { g_alias_fallback = 1; LOG("[RED] cheats: no writable alias of main, code pages go through an mprotect toggle that races with the game's own execution"); }
        for (uint64_t end = addr + len; addr < end;) {
            uint64_t p0 = addr & ~(uint64_t)(pg - 1), hi = p0 + pg < end ? p0 + pg : end;   // the slice of this page
            void *page = (void *)(uintptr_t)p0;
            int code = p0 < mb + rx_end || (p0 >= mb + po && p0 < mb + m->size);
            if (code) {
                if (mprotect(page, pg, PROT_READ | PROT_WRITE)) { cheat_kill(c, "mprotect of a code page failed (errno %d)", errno); return -1; }
                memcpy((void *)(uintptr_t)addr, v + (addr - start), hi - addr);
                if (mprotect(page, pg, PROT_READ | PROT_EXEC)) { cheat_kill(c, "mprotect restore failed (errno %d)", errno); return -1; }
            } else memcpy((void *)(uintptr_t)addr, v + (addr - start), hi - addr);
            addr = hi;
        }
    }
    sys_icache_invalidate((void *)(uintptr_t)start, len);   // the game's own fetches must see the new instructions
    return 0;
}

// dmnt's WriteCheatProcessMemoryUnsafe for this host: val's low len bytes, little-endian (guest aarch64 = host arm64),
// into the span. A refusal turns the cheat off (cheat_kill) and logs a [RED] line; the game keeps running. The guest
// address is logged as the cheat VM computes it (region base + rel + offset register), which is what the player reads
// in the cheat file's own terms
static void cheat_write(cheat_t *c, uint64_t addr, uint64_t len, uint64_t val) {
    int kind = -1;
    if (!span_get(addr, len, &kind, NULL)) { cheat_kill(c, "out of mapped memory: write to guest address 0x%llx", (unsigned long long)addr); return; }
    if (atomic_load(&g_dbg)) LOG("cheat \"%s\": write %llu bytes of 0x%llx at guest address 0x%llx (%s)", c->name, (unsigned long long)len, (unsigned long long)val, (unsigned long long)addr, kind == 0 ? "main NSO" : "heap");
    if (kind == 0) main_write_pages(c, addr, len, &val);
    // The heap write happens under the memory lock (dm_guest_heap_write), so a concurrent SetHeapSize cannot shrink it
    // out from under the copy; it only refuses if the span shrank since the span check a moment ago: out of range as ever
    else if (dm_guest_heap_write(addr, &val, len)) cheat_kill(c, "out of mapped memory: write to guest address 0x%llx", (unsigned long long)addr);
}

// dmnt's ReadCheatProcessMemoryUnsafe for this host: the mapped main span and the opened heap are both readable; the
// value is assembled zero-extended little-endian
static int cheat_read(cheat_t *c, uint64_t addr, uint64_t len, uint64_t *out) {
    int kind = -1;
    if (!span_get(addr, len, &kind, NULL)) { cheat_kill(c, "out of mapped memory: read at guest address 0x%llx", (unsigned long long)addr); return -1; }
    uint64_t v = 0;
    // The heap read is hole-free like its write counterpart: a span that shrank since the span check refuses here
    // instead of faulting on a page a concurrent SetHeapSize mprotect'd away
    if (kind == 1) { if (dm_guest_heap_read(addr, &v, len)) { cheat_kill(c, "out of mapped memory: read at guest address 0x%llx", (unsigned long long)addr); return -1; } }
    else memcpy(&v, (void *)(uintptr_t)addr, len);
    *out = v;
    return 0;
}

// ---------- the cheat VM: one pass ----------

static uint64_t g_reg[16], g_looptop[16];   // the reference's registers and loop tops (its saved values belong to C1/C2, not implemented)

// Region base for kind m: 0 main NSO, 1 heap. The caller checks region_ready(m) first: with no span open the base is
// 0, and a cheat resolved against 0 could by luck fall inside main's mapped span, which an out-of-range-style [RED]
// line then does not explain
static uint64_t region_base(int m) {
    if (m == 0) return g_main_mod ? (uint64_t)(uintptr_t)g_main_mod->base : 0;
    uint64_t hb; size_t hopen; dm_guest_heap_range(&hb, &hopen);
    return hb && hopen ? hb : 0;
}

// The named region must have its span open right now: a cheat that names the heap (region 1) before the game's first
// SetHeapSize would compute its addresses from base 0, so it is turned off here instead (it can simply be turned back
// on once the game has opened the heap — dead clears on reload)
static int region_ready(cheat_t *c, int m) {
    if (m == 0) return g_main_mod != NULL;   // main is always mapped by the time a cheat file was picked
    uint64_t hb; size_t hopen; dm_guest_heap_range(&hb, &hopen);
    if (!(hb && hopen)) { cheat_kill(c, "region 1 (heap) has no span opened yet"); return 0; }
    return 1;
}

// Skipping a failed / finished conditional the reference's way: walk nested begins and ends (each counted once at its
// decode), and a not-taken if also meets its else at the same depth as the skip's end (the else block is skipped too)
static int vm_skip(cheat_t *c, const uint32_t *ins, int nins, int *pidx, int *pdepth, int is_if) {
    int desired = *pdepth - 1;
    while (*pdepth > desired && *pidx < nins) {
        ins_t in;
        int len = ins_dec(c, ins + *pidx, nins - *pidx, &in);
        if (len <= 0) return -1;      // validated before the first pass; keep the walk safe anyway
        if (op_cond_begin(in.op)) (*pdepth)++;
        else if (in.op == 2) {
            if (!in.flags) (*pdepth)--;
            else if (is_if && *pdepth - 1 == desired) { *pidx += len; return 0; }   // an else of a not-taken if: stop there
        }
        *pidx += len;
    }
    return 0;
}

// The width's mask for conditions and arithmetic results (the reference truncates to the width)
static uint64_t width_mask(unsigned t) { return t == 8 ? UINT64_MAX : (1ull << (8 * t)) - 1; }

// One pass of cheat c; the VM state is whatever the caller reset. Returns -1 when the cheat killed itself (its
// word-boundary verdicts already marked it broken at load; a skip over a shuffled word could still fail here)
static int vm_run(cheat_t *c) {
    const uint32_t *ins = c->ins; int nins = c->nins;
    int idx = 0, depth = 0;   // like the reference Execute: one instruction pointer, one conditional depth
    long steps = 0;
    while (idx < nins) {
        if (++steps > VM_STEP_CAP) { cheat_kill(c, "over %d instructions in one pass: runaway loop", VM_STEP_CAP); return -1; }
        ins_t in;
        int len = ins_dec(c, ins + idx, nins - idx, &in);
        if (len <= 0) { cheat_kill(c, "malformed instruction at word %d%s", idx, c->why); return -1; }
        switch (in.op) {
            case 0: {   // static store: base + rel + reg[r] (the bounds check is the span check inside cheat_write)
                if (!region_ready(c, in.m)) return -1;
                cheat_write(c, region_base(in.m) + in.rel + g_reg[in.r], in.t, in.val & width_mask(in.t));
            } break;
            case 8: case 1: {   // key-press conditional (8) / memory conditional (1): depth counted like the reference, before the verdict
                depth++;
                int met = 1, run = 1;
                if (in.op == 8) {
                    met = (dm_cheats_keys() & in.val) == in.val;   // every key of the mask held
                } else {
                    if (!region_ready(c, in.m)) return -1;   // the conditional reads the region it names
                    uint64_t src = 0;
                    if (cheat_read(c, region_base(in.m) + in.rel + (in.flags ? g_reg[in.x] : 0), in.t, &src) == 0) {
                        uint64_t got = src & width_mask(in.t), want = in.val & width_mask(in.t);
                        // the six comparisons in the reference's number order: 1 >, 2 >=, 3 <, 4 <=, 5 ==, 6 !=
                        met = in.c == 1 ? got > want : in.c == 2 ? got >= want : in.c == 3 ? got < want :
                              in.c == 4 ? got <= want : in.c == 5 ? got == want : got != want;
                    } else run = 0;   // the read could not be done: the cheat is off (cheat_read logged the [RED] line)
                }
                if (!run) return -1;
                if (!met) { idx += len; if (vm_skip(c, ins, nins, &idx, &depth, 1)) return -1; continue; }   // block (else too) skipped
            } break;
            case 2:   // end / else of a conditional: an else skips its block, a plain end closes the block
                if (in.flags) {   // an else: skip its block like the reference; an else at depth 0 is mismatched, and
                                  // the reference treats that as a VM error (SkipConditionalBlock aborts at depth 0)
                    if (depth == 0) { cheat_kill(c, "mismatched else at conditional depth 0"); return -1; }
                    idx += len; if (vm_skip(c, ins, nins, &idx, &depth, 0)) return -1; continue;
                }
                if (depth > 0) depth--;   // a plain end (nop at depth 0, the reference's own gracious assumption)
                break;
            case 3:   // loop: start (counter set, jump-back point kept), end (decrement, jump back until it reaches 0)
                if (!in.flags) { g_reg[in.r] = in.val; g_looptop[in.r] = idx + 2; idx += (int)in.len; continue; }
                g_reg[in.r]--;
                if (g_reg[in.r]) { idx = (int)g_looptop[in.r]; continue; }
                break;
            case 4:   // register = static 64-bit value
                g_reg[in.r] = in.val;
                break;
            case 5: {   // register = the width bytes of one address (fixed, by register, or region + register, the reference's four forms)
                uint64_t addr, v0 = 0;
                switch (in.flags) {
                    case 0: if (!region_ready(c, in.m)) return -1; addr = region_base(in.m) + in.rel; break;
                    case 1: addr = g_reg[in.r] + in.rel; break;
                    case 2: addr = g_reg[in.x] + in.rel; break;
                    default: if (!region_ready(c, in.m)) return -1; addr = region_base(in.m) + g_reg[in.x] + in.rel; break;
                }
                if (cheat_read(c, addr, in.t, &v0) == 0) g_reg[in.r] = v0 & width_mask(in.t);
                else return -1;   // the load could not be done: the cheat is off (cheat_read logged it)
            } break;
            case 6: {   // store the value at reg[r] (+ reg[x] for o=1); reg[r] gains the width for I=1, like the reference
                cheat_write(c, g_reg[in.r] + (in.flags & 2 ? g_reg[in.x] : 0), in.t, in.val & width_mask(in.t));
                if (in.flags & 1) g_reg[in.r] += in.t;
            } break;
            case 7: {   // register arithmetic the reference's order: the full dword (its u64 zero-extension) goes into
                        // the operation and only the result is truncated to the width, as its ((u8)(reg - 0x100)) does
                        // (masking the operand to the width first happens to give the same add / sub / mul, but there
                        // is no reason to rely on that). The shift counts are masked to 63 bits, aarch64's LSLV / LSRV
                uint64_t v = in.val, r = g_reg[in.r];
                switch (in.c) {
                    case 0: r += v; break;   // 0 add
                    case 1: r -= v; break;   // 1 sub
                    case 2: r *= v; break;   // 2 mul
                    case 3: r <<= (v & 63); break;   // 3 lsl
                    case 4: r >>= (v & 63); break;   // 4 lsr
                }
                g_reg[in.r] = r & width_mask(in.t);
            } break;
            default:
                cheat_kill(c, "instruction the VM does not run reached it");   // cannot happen: validation turned the cheat off
                return -1;
        }
        idx += len;
    }
    return 0;
}

// ---------- the pass, the present hook and the idle thread ----------

// One pass: the masters first, then the enabled cheats in file order. The VM state (registers, loop tops) is fresh each
// pass, the reference's ResetState over its concatenated program. The lock is never waited for: a pass that arrives
// while a menu operation or another pass runs is simply skipped (the next frame / tick applies again)
static void cheats_pass(void) {
    if (!atomic_load(&g_active)) return;
    if (pthread_mutex_trylock(&g_lock)) return;
    for (int half = 0; half < 2; half++) for (int i = 0; i < g_ncheat; i++) {
        cheat_t *c = &g_cheat[i];
        if (c->broken || c->dead) continue;
        if ((half == 0) != (c->master != 0)) continue;   // half 0 = masters, half 1 = the enabled plain cheats
        if (half && !c->on) continue;
        memset(g_reg, 0, sizeof g_reg); memset(g_looptop, 0, sizeof g_looptop);   // the reference's per-pass register reset
        vm_run(c);
    }
    pthread_mutex_unlock(&g_lock);
}

// Per presented frame (hle_nvn.c dump_frame): apply the cheats and note the present, so the idle thread stands down
// (brief: once per presented frame; the idle thread only when it is not presenting)
void dm_cheats_present(void) {
    atomic_store(&g_present_ns, now_ns());
    cheats_pass();
}

// The fixed ~60 Hz passes when the game is not presenting (window minimized, graphics suspended or before the first
// present): a stopped game still changes under its cheats, as on hardware where the cheat process keeps running
static void *cheat_tick_thread(void *arg) {
    (void)arg;
    while (atomic_load(&g_inited)) {
        usleep(16667);   // ~60 Hz
        if (now_ns() - atomic_load(&g_present_ns) < 250000000ull) continue;   // presenting again: the hook applies
        cheats_pass();
    }
    return NULL;
}

// ---------- the cheat states: the saved <build>.enabled file and the DM_CHEATS_ON switch ----------

// Save the enabled states: one non-master cheat name per line, <build>.enabled in the cheats folder (masters are
// always on). Rewritten on every menu toggle, read at each load
static void states_save(void) {
    if (!g_dir[0] || !g_build[0]) return;
    char path[1400]; snprintf(path, sizeof path, "%s/%s.enabled", g_dir, g_build);
    FILE *f = fopen(path, "w");
    if (!f) { LOG("cheats: cannot write %s (errno %d)", path, errno); return; }
    for (int i = 0; i < g_ncheat; i++) if (g_cheat[i].on && !g_cheat[i].master) fprintf(f, "%s\n", g_cheat[i].name);
    fclose(f);
}

// Restore the states: the saved file's names first (exact, as written), then DM_CHEATS_ON's (name for name,
// case-insensitive, as the brief lets sites write the names); neither writes a master, they are always on
static void states_load(void) {
    if (g_dir[0]) {
        char path[1400]; snprintf(path, sizeof path, "%s/%s.enabled", g_dir, g_build);
        FILE *f = fopen(path, "r");
        if (f) {
            char line[1024];
            while (fgets(line, sizeof line, f)) {
                char *n = strtok(line, "\r\n");
                if (!n) continue;
                for (int i = 0; i < g_ncheat; i++) if (!g_cheat[i].master && !strcmp(g_cheat[i].name, n)) g_cheat[i].on = 1;
            }
            fclose(f);
        }
    }
    for (int k = 0; k < g_non; k++)
        for (int i = 0; i < g_ncheat; i++)
            if (!g_cheat[i].master && !strcasecmp(g_cheat[i].name, g_on[k])) g_cheat[i].on = 1;
}

// The menu's toggle: flip the cheat, save the states
void dm_cheat_toggle(int i) {
    if (i < 0 || i >= g_ncheat) return;
    pthread_mutex_lock(&g_lock);
    cheat_t *c = &g_cheat[i];
    if (!c->master && !c->broken && !c->dead) { c->on = !c->on; states_save(); }
    pthread_mutex_unlock(&g_lock);
}

// ---------- loading: the folder, the build's file, the parse ----------

// The folders scanned, in the brief's order: the flat folder, the Atmosphère tree under it
// (atmosphere/contents/<tid>/cheats) and the tree with the folder itself as the "atmosphere" half (contents/<tid>/cheats)
static int scan_dirs(char out[3][1024]) {
    if (!g_dir[0] || !g_tid[0]) return 0;
    snprintf(out[0], 1024, "%s", g_dir);
    snprintf(out[1], 1024, "%s/atmosphere/contents/%s/cheats", g_dir, g_tid);
    snprintf(out[2], 1024, "%s/contents/%s/cheats", g_dir, g_tid);
    return 3;
}

// Does the file name hold exactly this build ID (any case), as the atmosphere loader names its cheat files?
static int name_is_build(const char *name, const char *build) {
    for (int k = 0; k < 16; k++) {
        char a = name[k], b = build[k];
        if (!a) return 0;
        a = (char)tolower((unsigned char)a); b = (char)tolower((unsigned char)b);
        if (a != b) return 0;
    }
    return (int)strlen(name) >= 16 && (name[16] == '.' || !name[16]);
}

// The first 16 characters as a hex build ID (for the other-build list)? "another version of the game" needs a real
// build ID name, so hunks like "readme.txt" do not show up as builds
static int name_hex16(const char *name) {
    if (strlen(name) < 16) return 0;
    for (int k = 0; k < 16; k++) {
        char a = (char)tolower((unsigned char)name[k]);
        if (!((a >= '0' && a <= '9') || (a >= 'a' && a <= 'f'))) return 0;
    }
    return 1;
}

static char g_cand[CAND_MAX][2048]; static int g_ncand;

// Collect the .txt files of one folder (case-insensitive suffix, .enabled ignored), deduped by path
static void collect_dir(const char *dir_) {
    DIR *d = opendir(dir_);
    if (!d) return;
    struct dirent *e;
    while ((e = readdir(d))) {
        size_t n = strlen(e->d_name);
        if (n < 5 || strcasecmp(e->d_name + n - 4, ".txt")) continue;
        if (g_ncand >= CAND_MAX) break;
        char *p = g_cand[g_ncand];
        snprintf(p, 2048, "%s/%s", dir_, e->d_name);
        int dup = 0;
        for (int i = 0; i < g_ncand; i++) if (!strcmp(g_cand[i], p)) { dup = 1; break; }
        if (!dup) g_ncand++;
    }
    closedir(d);
}

// Parse the file into the cheats array; lines "others" than [Name] / {Name} headers and 8-hex-digit code words
// separated by spaces are ignored (the brief), with one [RED] line for a line whose words are code-like but not valid
static void parse_file(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { LOG("[RED] cheats: cannot read %s (errno %d)", path, errno); return; }
    char line[4096];
    cheat_t *cur = NULL;
    int lineno = 0, warned = 0;
    while (fgets(line, sizeof line, f)) {
        lineno++;
        char *p = line;
        while (*p == ' ' || *p == '\t') p++;
        char end = 0;
        if (*p == '[') end = ']';
        else if (*p == '{') end = '}';
        if (end) {   // a header starts a new cheat; the name is what lies inside
            char *q = strchr(p, end);
            size_t nl = q && q > p ? (size_t)(q - p - 1) : 0;
            if (nl == 0 || g_ncheat >= CHEAT_MAX) {
                if (g_ncheat >= CHEAT_MAX && !warned++) LOG("[RED] cheats: more than %d cheats in %s, the rest is skipped", CHEAT_MAX, path);
                cur = NULL;
                continue;
            }
            cur = &g_cheat[g_ncheat++];
            memset(cur, 0, sizeof *cur);
            // the name keeps NAME_MAX - 1 characters: a shorter cut once let two long-named cheats share a line in <build>.enabled
            snprintf(cur->name, NAME_MAX, "%.*s", (int)(nl > 127 ? 127 : nl), p + 1);
            cur->master = end == '}';
            cur->on = cur->master;
            continue;
        }
        if (!cur) continue;   // words before any [Name] / {Name} header belong to nothing: the line is ignored (site files carry prose)
        // the words of the line: whole tokens of exactly 8 hex digits; anything else makes the line prose
        uint32_t got[INS_MAX]; int ngot = 0, bad = 0;
        const char *badt = "";   // the token that is not a word, named on the [RED] line
        for (char *t = strtok(p, " \t\r\n"); t; t = strtok(NULL, " \t\r\n")) {
            if (strlen(t) != 8) { bad = 1; badt = t; break; }
            uint32_t w = 0;
            for (int k = 0; k < 8; k++) {
                char a = (char)tolower((unsigned char)t[k]);
                unsigned d = a >= '0' && a <= '9' ? (unsigned)(a - '0') : a >= 'a' && a <= 'f' ? (unsigned)(a - 'a' + 10) : 16;
                if (d == 16) { bad = 1; badt = t; break; }
                w = w << 4 | d;
            }
            if (bad) break;
            if (ngot < INS_MAX) got[ngot++] = w;
            else { LOG("[RED] cheat \"%s\": line %d has more than %d code words, the rest of the line is ignored", cur->name, lineno, INS_MAX); break; }
        }
        if (!ngot && !bad) continue;   // only whitespace
        if (bad && !ngot) {   // the file format ignores the line (the brief's "other lines"): prose, once warned
            if (!warned++) LOG("[RED] cheats: %s line %d is not code words and is ignored", path, lineno);
            continue;
        }
        if (bad) {
            // words would be dropped from a line that held them: the dropped token may carry an instruction of its
            // own (a vanished begin or end leaves the body running every frame unconditionally), so the cheat stays
            // off entirely instead of silently running a fragment of itself; once per cheat, with the token named
            if (!cur->broken) {
                cur->broken = 1; snprintf(cur->why, sizeof cur->why, " (malformed line %d)", lineno);
                LOG("[RED] cheats: %s: \"%s\" line %d mixes code words with \"%s\", the cheat stays off", path, cur->name, lineno, badt);
            }
            continue;
        }
        if (cur->nins + ngot > INS_MAX) { LOG("[RED] cheat \"%s\": over %d code words, skipped", cur->name, INS_MAX); continue; }
        memcpy(cur->ins + cur->nins, got, sizeof(uint32_t) * (size_t)ngot);
        cur->nins += ngot;
    }
    fclose(f);
    // The verdict per cheat: no code words at all is an empty cheat; anything else is decoded word by word, and one
    // instruction the VM does not run (unsupported opcode, region, width, condition) or the words ending inside a
    // field turns the whole cheat off, shown in the menu with the reason, never run
    for (int i = 0; i < g_ncheat; i++) {
        cheat_t *c = &g_cheat[i];
        if (c->broken) continue;   // already off with its own reason (a malformed line): the decode would overwrite why
        if (c->nins == 0) { c->broken = 1; snprintf(c->why, sizeof c->why, " (empty)"); continue; }
        for (int a = 0; a < c->nins;) {
            ins_t in;
            int len = ins_dec(c, c->ins + a, c->nins - a, &in);
            if (len <= 0) break;   // the reason is already in c->why and c->broken is set
            a += len;
        }
    }
}

// (Re)load: choose the file, note the other builds, parse, restore the states. Called at init and from "Reload cheats"
static void load_all(void) {
    g_ncheat = 0; g_ncand = 0; g_nothers = 0; g_path[0] = 0;
    atomic_store(&g_active, 0);
    char dirs[3][1024]; int nd = scan_dirs(dirs);
    for (int i = 0; i < nd; i++) collect_dir(dirs[i]);
    if (!g_build[0]) { LOG("[RED] cheats: the main NSO has no build ID, so no file can be picked from %s", g_dir); return; }
    int pick = -1, other = 0;   // pick = the matching candidate; other = when a non-matching one is used by DM_CHEATS_ANY_BUILD
    for (int i = 0; i < g_ncand; i++) {   // the whole list is walked: the build's file may lie after an "another version" one
        const char *nm = strrchr(g_cand[i], '/') + 1;
        int hex = name_hex16(nm);
        if (!hex) continue;
        if (name_is_build(nm, g_build)) {
            if (pick < 0) pick = i;   // the first matching candidate wins (the flat folder, then the Atmosphere tree)
            continue;   // keep walking: the other builds get collected below either way
        }
        // the other versions of the game (max OTHER_MAX, the menu shows them disabled)
        int dup = 0;
        for (int k = 0; k < g_nothers; k++) if (!strncasecmp(g_others[k], nm, 16)) { dup = 1; break; }
        if (!dup && g_nothers < OTHER_MAX) snprintf(g_others[g_nothers++], 17, "%s", nm);
    }
    if (pick < 0 && !(g_any && g_ncand == 1)) {
        LOG("cheats: %s: no file for build %s", g_dir, g_build);
        if (g_nothers && atomic_load(&g_dbg)) {   // the menu's "another version" rows, this file's context
            char list[OTHER_MAX * 18]; list[0] = 0;
            for (int i = 0; i < g_nothers; i++) { strlcat(list, " ", sizeof list); strlcat(list, g_others[i], sizeof list); }
            LOG("cheats: %s: %d .txt of other builds in the folder:%s", g_dir, g_nothers, list);
        }
        return;
    }
    if (pick < 0) { pick = 0; other = 1; }   // DM_CHEATS_ANY_BUILD and a single non-matching file: load it
    g_nothers = 0;   // a file is loaded (this build's own, or DM_CHEATS_ANY_BUILD's): no "another version" rows
    snprintf(g_path, sizeof g_path, "%s", g_cand[pick]);
    // The writable alias of main is mapped once a cheat file is actually picked, not at init merely because DM_ROOT is
    // set: a run without cheats would otherwise always map a second image of main and log a line for it. At init the
    // pick happens before the guest starts; a later "Reload cheats" retries only when no alias mapped the first time
    if (g_main_mod && !g_alias) {
        alias_setup();
        LOG("cheats: writable alias of main %s", g_alias ? "mapped" : "not mapped (mprotect toggle fallback)");
    }
    parse_file(g_path);
    states_load();
    // the summary: masters are always on, a broken / empty cheat never runs, the rest keep the menu's saved state
    int on = 0, bad = 0, masters = 0;
    for (int i = 0; i < g_ncheat; i++) {
        if (g_cheat[i].master) masters++;
        if (g_cheat[i].broken) bad++;
        else if (!g_cheat[i].master && g_cheat[i].on) on++;
    }
    if (other) LOG("[RED] cheats: no file for build %s, loading %s of another build on DM_CHEATS_ANY_BUILD: its addresses may be wrong", g_build, g_cand[pick]);
    LOG("cheats: %s: build %s: %d cheats (%d master, %d on, %d broken, %d runnable)", g_path, g_build, g_ncheat, masters, on, bad, g_ncheat - bad);
    atomic_store(&g_active, g_ncheat > 0);
}

// Read the switches, find the game's file, load it, and start the idle apply thread. Called after load_modules
// (main.c host_preload): the build ID to pick the file by comes from the modules them
void dm_cheats_init(void) {
    atomic_store(&g_dbg, !!getenv("DM_CHEATS_DEBUG"));
    const char *e = getenv("DM_CHEATS_ANY_BUILD"); g_any = e && *e && atoi(e) != 0;
    e = getenv("DM_CHEATS");
    if (e && *e) snprintf(g_dir, sizeof g_dir, "%s", e);
    else { e = getenv("DM_ROOT"); if (e && *e) snprintf(g_dir, sizeof g_dir, "%s/cheats", e); }
    snprintf(g_tid, sizeof g_tid, "%016llX", (unsigned long long)DM_GAME_PROGRAM_ID);
    // g_build: the main NSO's first 16 hex digits, upper case like the menu and the brief state them; the candidate
    // match itself is case-insensitive (name_is_build lower-cases both sides)
    const char *bid = dm_main_build();
    if (strlen(bid) >= 16) {
        for (int k = 0; k < 16; k++) g_build[k] = (char)toupper((unsigned char)bid[k]);
        g_build[16] = 0;
    }
    e = getenv("DM_CHEATS_ON");
    if (e && *e) {   // one-off names turned on at launch, split on ','; the saves' own <build>.enabled states stay too
        char *dup = strdup(e), *s = dup;
        while (s && g_non < 16) {
            char *t = strchr(s, ',');
            if (t) *t = 0;
            if (*s) snprintf(g_on[g_non++], NAME_MAX, "%s", s);
            s = t ? t + 1 : NULL;
        }
        free(dup);
    }
    if (!g_dir[0]) { LOG("cheats: off (neither DM_CHEATS nor DM_ROOT is set)"); }
    else {   // for the main module the pass needs its base: the loader's g_mod tables them by name
        for (int i = 0; i < g_nmod; i++) if (!strcmp(g_mod[i].name, "main") && !g_mod[i].nro) { g_main_mod = &g_mod[i]; break; }
        if (g_main_mod) { pthread_mutex_lock(&g_lock); load_all(); pthread_mutex_unlock(&g_lock); }   // load_all maps the writable alias once a file is picked
    }
    atomic_store(&g_inited, 1);
    pthread_t th; pthread_attr_t a; pthread_attr_init(&a); pthread_attr_setdetachstate(&a, PTHREAD_CREATE_DETACHED);
    // The idle thread always runs (it stands down while the presents are recent, and a later "Reload cheats" that
    // brings cheats in must also get its idle passes)
    if (pthread_create(&th, &a, cheat_tick_thread, NULL)) LOG("[RED] cheats: cannot start the ~60 Hz apply thread (errno %d), only presents apply", errno);
    pthread_attr_destroy(&a);
}

// ---------- the Mac cheats menu (callers: front_mac.m; nothing else uses these) ----------
// Cheap accessors read straight from the shared state: the list itself is rebuilt only from the main thread (this
// menu's own actions, and init on the Mac's main thread), and a VM pass mutates only its own cheat's dead / why
// flags, whose worst-case tear shows as one truncated reason in a row rebuilt in that instant

int dm_cheats_found(void) { return atomic_load(&g_active) || g_ncheat > 0; }   // a file, of this build or another

int dm_cheats_ncheats(void) { return g_ncheat; }

const char *dm_cheats_build(void) { return g_build; }   // static after init

const char *dm_cheats_dir_path(void) { return g_dir; }   // "" when neither DM_CHEATS nor DM_ROOT is set

int dm_cheats_nothers(void) { return g_nothers; }

const char *dm_cheats_other(int i) { return i >= 0 && i < g_nothers ? g_others[i] : ""; }

const char *dm_cheat_name_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].name : ""; }

const char *dm_cheat_why_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].why : ""; }

// The row's kind, for the menu's builder: 0 = a plain cheat (click toggles), 1 = master (always on, no click),
// 2 = broken / off (disabled). The checkmark itself: dm_cheat_on_at
int dm_cheat_kind_at(int i) {
    if (i < 0 || i >= g_ncheat) return 2;
    return g_cheat[i].broken || g_cheat[i].dead ? 2 : g_cheat[i].master ? 1 : 0;
}

int dm_cheat_on_at(int i) { return i >= 0 && i < g_ncheat ? g_cheat[i].on != 0 : 0; }

// "Reload cheats": re-read the file (the same path), so edits during play do not need a re-launch
void dm_cheats_reload(void) {
    pthread_mutex_lock(&g_lock);
    load_all();
    pthread_mutex_unlock(&g_lock);
}
