#define LF_X11
#define LF_RUNARA
#include <sys/ioctl.h>
#include <X11/Xlib.h>
#include <string.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <pty.h>
#include <sys/select.h>
#include <unistd.h>
#include <stdbool.h>
#include <errno.h>
#include <ctype.h>
#include <leif/leif.h>
#include <leif/win.h>
#include <leif/ui_core.h>

#define MAX_ROWS 4096
#define CLAMP(val, min, max) ((val) < (min) ? (min) : ((val) > (max) ? (max) : (val)))

static int32_t masterfd;

typedef struct
{
    uint32_t codepoint;
} Cell;

typedef struct
{
    uint32_t x, y;
} TermCursor;

typedef struct
{
    char buf[128 * 4];
    size_t len;
    char prefix;
    int params[16];
    uint32_t nparams;
    char cmd[2];
} CsiEscapeSeq;

typedef enum
{
    ESC_STATE_ON_ESC = 1,
    ESC_STATE_CSI = 2,
    ESC_STATE_STR = 4,
    ESC_STATE_ALTCHARSET = 8,
    ESC_STATE_STR_END = 16,
    ESC_STATE_TEST = 32,
    ESC_STATE_UTF8 = 64,
} EscapeState;

typedef enum
{
    CUR_STATE_NORMAL = 1,
    CUR_STATE_ONWRAP = 2,
    CUR_STATE_ORIGIN = 4,
} CursorState;

typedef enum
{
    TERM_MODE_CURSOR_KEYS = 1 << 0,
    TERM_MODE_REVERSE_VIDEO = 1 << 1,
    TERM_MODE_AUTO_WRAP = 1 << 2,
    TERM_MODE_HIDE_CURSOR = 1 << 3,
    TERM_MODE_MOUSE = 1 << 4,
    TERM_MODE_MOUSE_X10 = 1 << 5,
    TERM_MODE_MOUSE_REPORT_BTN = 1 << 6,
    TERM_MODE_MOUSE_REPORT_MOTION = 1 << 7,
    TERM_MODE_MOUSE_REPORT_ALL_EVENTS = 1 << 8,
    TERM_MODE_MOUSE_REPORT_SGR = 1 << 9,
    TERM_MODE_REPORT_FOCUS = 1 << 10,
    TERM_MODE_8BIT = 1 << 11,
    TERM_MODE_ALTSCREEN = 1 << 12,
    TERM_MODE_BRACKETED_PASTE = 1 << 13,
    TERM_MODE_INSERT = 1 << 14,
    TERM_MODE_LOCK_KEYBOARD = 1 << 15,
    TERM_MODE_ECHO = 1 << 16,
    TERM_MODE_CR_AND_LF = 1 << 17,
    TERM_MODE_UTF8 = 1 << 17, // Note: This shares the same bit as CR_AND_LF
} termmode_t;

static uint32_t escflags;
static uint32_t termflags;
static CursorState cursorstate;
static CsiEscapeSeq csiseq;
static TermCursor cursor, cursor_saved;
static Cell *main_cells = NULL;
static Cell *alt_cells = NULL;
static Cell *cells = NULL; // The active lens pointing to either main or alt
static bool alt_buffer_active = false;
static uint32_t rows = 20;
static uint32_t cols = 80;
static lf_ui_state_t *ui;
static lf_mapped_font_t font;
static uint32_t *tabs;
static uint32_t scrollbottom, scrollbottom_saved = 0;
static uint32_t scrolltop, scrolltop_saved = 0;
static uint32_t head, head_saved = 0;
static uint32_t mostrecentcodepoint;

static void moveto(int32_t x, int32_t y);
static void scrollup(int32_t start, int32_t nscrolls);
static void handlecodepoint(uint32_t codepoint);
static void termwrite(const char *buf, size_t len, bool mayecho);
static void scrolldown(int32_t start, int32_t nscrolls);
static Cell *getphysrow(int32_t logicalrow);
static void clearcell(Cell *cell);
static void handletab(int32_t count);
static void deletecells(int32_t ncells);

void newline(bool setx)
{
    int32_t x = setx ? 0 : cursor.x;
    int32_t y = cursor.y;
    if (y == scrollbottom)
    {
        scrollup(scrolltop, 1);
    }
    else
    {
        y++;
    }
    moveto(x, y);
}

void handlealtcursor(bool restore)
{
    if (!restore)
    {
        cursor_saved = cursor;
        scrollbottom_saved = scrollbottom;
        scrolltop_saved = scrolltop;
        head_saved = head;
    }
    else
    {
        cursor = cursor_saved;
        scrollbottom = scrollbottom_saved;
        scrolltop = scrolltop_saved;
        head = head_saved;
        moveto(cursor.x, cursor.y);
    }
}

void moveto(int32_t x, int32_t y)
{
    int32_t miny = 0, maxy = rows - 1;
    if (lf_flag_exists(&cursorstate, CUR_STATE_ORIGIN))
    {
        miny = scrolltop;
        maxy = scrollbottom;
    }
    cursor.x = CLAMP(x, 0, cols - 1);
    cursor.y = CLAMP(y, miny, maxy);
    lf_flag_unset(&cursorstate, CUR_STATE_ONWRAP);
}

void movetosafe(int32_t x, int32_t y)
{
    bool cursororigin = lf_flag_exists(&cursorstate, CUR_STATE_ORIGIN);
    moveto(x, y + (cursororigin ? scrolltop : 0));
}

void setcell(uint32_t x, uint32_t y, uint32_t codepoint)
{
    cells[y * cols + x].codepoint = codepoint;
}

bool iscontrol(uint32_t c)
{
    if (((int32_t)c >= 0x00 && c <= 0x1F) || c == 0x7F)
        return true;
    if (c >= 0x80 && c <= 0x9F)
        return true;

    return false;
}

bool iscontrolc1(uint32_t c)
{
    if (c >= 0x80 && c <= 0x9F)
        return true;
    return false;
}

void handlectrl(uint32_t c)
{
    switch (c)
    {
    case '\f':
    case '\v':
    case '\n':
        newline(true);
        break;
    case '\t':
        handletab(1);
        break;
    case '\b':
        moveto(cursor.x - 1, cursor.y);
        return;
    case '\r':
    {
        moveto(0, cursor.y);
        return;
    }
    case 0x7f:
    {
        deletecells(1);
        break;
    }
    case 0x88:
    {
        // insert tabstop
        break;
    }
    case 0x85:
    {
        newline(true);
        break;
    }
    case '\033':
    {
        memset(&csiseq, 0, sizeof(csiseq));
        lf_flag_unset(&escflags, ESC_STATE_CSI | ESC_STATE_ALTCHARSET | ESC_STATE_TEST);
        lf_flag_set(&escflags, ESC_STATE_ON_ESC);
        return;
    }
    case '\032':
    {
        setcell(cursor.x, cursor.y, '?');
        break;
    }
    default:
        lf_flag_unset(&escflags, ESC_STATE_STR_END | ESC_STATE_STR);
        break;
    }
}

bool handleescseq(uint32_t c)
{
    switch (c)
    {
    case '[':
    {
        lf_flag_set(&escflags, ESC_STATE_CSI);
        return true;
    }
    case '#':
    {
        lf_flag_set(&escflags, ESC_STATE_TEST);
        return true;
    }
    case '%':
    {
        lf_flag_set(&escflags, ESC_STATE_UTF8);
        return true;
    }
    case ']':
    case 'P':
    case '_':
    case '^':
    case 'k':
    {
        lf_flag_set(&escflags, ESC_STATE_STR);
        return true;
    }
    case 'n':
    case 'o':
        break;
    case '(':
    case ')':
    case '*':
    case '+':
    {
        lf_flag_set(&escflags, ESC_STATE_ALTCHARSET);
        return true;
    }
    case 'D':
    {
        newline(false);
        break;
    }
    case 'E':
    {
        newline(true);
        break;
    }
    case 'H':
    {
        tabs[cursor.x] = 1;
        break;
    }
    case 'M':
    {
        if (cursor.y == scrolltop)
        {
            scrolldown(scrolltop, 1);
        }
        else
        {
            moveto(cursor.x, cursor.y - 1);
        }
        break;
    }
    case 'Y':
    {
        // identify terminal
        break;
    }
    case 'c':
    {
        // reset state
        break;
    }
    case '>':
    {
        // normal keypad
        break;
    }
    case '7':
    {
        handlealtcursor(false);
        break;
    }
    case '8':
    {
        handlealtcursor(true);
        break;
    }
    case '\\':
    {
        // string terminator
        break;
    }
    default:
        break;
    }

    return false;
}

void parsecsi(void)
{
    if (!csiseq.len)
        return;
    csiseq.buf[csiseq.len] = '\0';
    uint32_t i = 0;
    if (csiseq.buf[i] == '?')
    {
        csiseq.prefix = csiseq.buf[i];
        i++;
    }
    else
    {
        csiseq.prefix = '\0';
    }

    char argbuf[32];
    uint32_t argidx = 0;
    for (; i < csiseq.len; i++)
    {
        // SECURE: Hard boundary set to 16 to perfectly match the struct capacity
        if (csiseq.nparams >= 16)
            break;

        if (isdigit(csiseq.buf[i]))
        {
            if (argidx < sizeof(argbuf) - 1)
            {
                argbuf[argidx++] = csiseq.buf[i];
            }
        }
        else if (csiseq.buf[i] == ';')
        {
            argbuf[argidx] = '\0';
            csiseq.params[csiseq.nparams++] = atoi(argbuf);
            memset(argbuf, 0, sizeof(argbuf));
            argidx = 0;
        }
        else
        {
            break;
        }
    }

    // SECURE: Final check before writing the last trailing parameter
    if (argidx > 0 && csiseq.nparams < 16)
    {
        argbuf[argidx] = '\0';
        csiseq.params[csiseq.nparams++] = atoi(argbuf);
    }

    csiseq.cmd[0] = csiseq.buf[i];
    if (i + 1 <= csiseq.len - 1)
    {
        csiseq.cmd[1] = csiseq.buf[i + 1];
    }
}

Cell *cellat(int32_t x, int32_t y)
{
    int32_t physrow = (head + y) % MAX_ROWS;
    return &cells[physrow * cols + x];
}

void deletecells(int32_t ncells)
{
    if (ncells <= 0 || cursor.x >= cols)
        return;

    if (cursor.x + ncells > cols)
        ncells = cols - cursor.x;

    Cell *cursorrow = getphysrow(cursor.y);

    int32_t src = cursor.x + ncells;
    int32_t dest = cursor.x;
    int32_t n = cols - src;
    memmove(
        &cursorrow[dest],
        &cursorrow[src], n * sizeof(Cell));

    // Clear the trailing garbage characters after the move
    for (int32_t x = cols - ncells; x < cols; x++)
    {
        clearcell(&cursorrow[x]);
    }
}

void insertblankchars(int32_t nchars)
{
    if (nchars <= 0 || cursor.x >= cols)
        return;

    if (cursor.x + nchars > cols)
        nchars = cols - cursor.x;

    Cell *cursorrow = getphysrow(cursor.y);

    int32_t src = cursor.x;
    int32_t dest = cursor.x + nchars;
    int32_t n = cols - dest;

    // Shift right
    memmove(
        &cursorrow[dest],
        &cursorrow[src], n * sizeof(Cell));

    // Insert blank cells
    for (int32_t x = src; x < dest; x++)
    {
        clearcell(&cursorrow[x]);
    }
}

void handletab(int32_t count)
{
    int32_t x = cursor.x;

    if (count > 0)
    {
        for (int32_t i = 0; i < count && x < cols - 1; ++i)
        {
            ++x;
            while (x < cols && !tabs[x])
            {
                ++x;
            }
        }
    }
    else if (count < 0)
    {
        for (int32_t i = 0; i < -count && x > 0; ++i)
        {
            --x;
            while (x > 0 && !tabs[x])
            {
                --x;
            }
        }
    }
    if (x >= cols)
        x = cols - 1;
    if (x < 0)
        x = 0;
    cursor.x = x;
}

void handlecsi(void)
{
    uint32_t dp = csiseq.nparams > 0 ? csiseq.params[0] : 1;
    switch (csiseq.cmd[0])
    {
    case 'b':
    {
        uint32_t n = MIN(dp, SHRT_MAX);
        for (uint32_t i = 0; i < n; i++)
        {
            handlecodepoint(mostrecentcodepoint);
        }
        break;
    }
    case '@':
    {
        insertblankchars(dp);
        break;
    }
    case 'A':
    {
        moveto(cursor.x, cursor.y - dp);
        break;
    }
    case 'B':
    case 'e':
    {
        moveto(cursor.x, cursor.y + dp);
        break;
    }
    case 'C':
    case 'a':
    {
        moveto(cursor.x + dp, cursor.y);
        break;
    }
    case 'D':
    {
        moveto(cursor.x - dp, cursor.y);
        break;
    }
    case 'E':
    {
        moveto(0, cursor.y + dp);
        break;
    }
    case 'F':
    {
        moveto(0, cursor.y - dp);
        break;
    }
    case 'g':
    {
        switch (csiseq.params[0])
        {
        case 0:
            tabs[cursor.x] = 0;
            break;
        case 3:
            memset(tabs, 0, sizeof(uint32_t) * cols);
            break;
        default:
            break;
        }
        break;
    }
    case 'G':
    case '`':
    {
        moveto(dp - 1, cursor.y);
        break;
    }
    case 'H':
    case 'f':
    {
        uint32_t x = csiseq.nparams > 1 ? csiseq.params[1] : 1;
        uint32_t y = csiseq.nparams > 0 ? csiseq.params[0] : 1;
        movetosafe(x - 1, y - 1);
        break;
    }
    case 'I':
    {
        handletab(dp);
        break;
    }
    case 'K':
    {
        int32_t op = csiseq.params[0];
        if (op == 0)
        {
            for (int32_t x = cursor.x; x < cols; x++)
            {
                clearcell(cellat(x, cursor.y));
            }
        }
        else if (op == 1)
        {
            for (int32_t x = 0; x < cursor.x; x++)
            {
                clearcell(cellat(x, cursor.y));
            }
        }
        else if (op == 2)
        {
            for (int32_t x = 0; x < cols; x++)
            {
                clearcell(cellat(x, cursor.y));
            }
        }
        break;
    }
    case 'J':
    {
        int32_t op = csiseq.params[0];
        if (op == 0)
        {
            for (int32_t x = cursor.x; x < cols; x++)
            {
                clearcell(cellat(x, cursor.y));
            }
            if (cursor.y >= rows - 1)
                break;
            for (int32_t y = cursor.y + 1; y < rows; y++)
            {
                for (int32_t x = 0; x < cols; x++)
                {
                    clearcell(cellat(x, y));
                }
            }
        }
        else if (op == 1)
        {
            if (cursor.y > 1)
            {
                for (int32_t y = 0; y < cursor.y - 1; y++)
                {
                    for (int32_t x = 0; x < cols; x++)
                    {
                        clearcell(cellat(x, y));
                    }
                }
            }
            for (int32_t x = 0; x < cursor.x; x++)
            {
                clearcell(cellat(x, cursor.y));
            }
        }
        else if (op == 2)
        {
            for (int32_t y = 0; y < rows; y++)
            {
                for (int32_t x = 0; x < cols; x++)
                {
                    clearcell(cellat(x, y));
                }
            }
        }
        break;
    }
    case 'S':
    {
        if (csiseq.prefix == '?')
            break;
        scrollup(scrolltop, dp);
        break;
    }
    case 'T':
    {
        scrolldown(scrolltop, dp);
        break;
    }
    case 'L':
    {
        if (scrolltop <= cursor.y && cursor.y <= scrollbottom)
        {
            scrolldown(cursor.y, dp);
        }
        break;
    }
    case 'M':
    {
        if (scrolltop <= cursor.y && cursor.y <= scrollbottom)
        {
            scrollup(cursor.y, dp);
        }
        break;
    }
    case 'X':
    {
        for (int32_t x = cursor.x; x < cursor.x + dp && x < cols; x++)
        {
            clearcell(cellat(x, cursor.y));
        }
        break;
    }
    case 'P':
    {
        deletecells(dp);
        break;
    }
    case 'Z':
    {
        handletab(-dp);
        break;
    }
    case 'd':
    {
        movetosafe(cursor.x, dp - 1);
        break;
    }
    case 'r':
    {
        if (csiseq.prefix == '?')
            break;
        // Check nparams, then pull from the params array
        uint32_t top = csiseq.nparams > 0 ? csiseq.params[0] - 1 : 0;

        // FIX: Change csiseq.params > 1 to csiseq.nparams > 1
        uint32_t bottom = csiseq.nparams > 1 ? csiseq.params[1] - 1 : rows - 1;

        scrolltop = top;
        scrollbottom = bottom;
        movetosafe(0, 0);
        break;
    }
    case 's':
    {
        handlealtcursor(false);
        break;
    }
    case 'u':
    {
        handlealtcursor(true);
        break;
    }
    case 'h':
    {
        // 1049 is the standard code to save cursor and switch to Alt Buffer
        if (csiseq.prefix == '?' && csiseq.params[0] == 1049)
        {
            if (!alt_buffer_active)
            {
                alt_buffer_active = true;
                handlealtcursor(false); // Save main buffer's cursor and scroll state
                cells = alt_cells;      // Swap the lens to the Alt Buffer
                head = 0;               // Reset circular buffer offset for a clean slate

                // --- ADD THESE 4 LINES ---
                // Give the new buffer a perfectly clean slate
                scrolltop = 0;
                scrollbottom = rows - 1;
                cursor.x = 0;
                cursor.y = 0;
                // -------------------------

                // Erase anything left over in the Alt Buffer from the last app
                for (int y = 0; y < rows; y++)
                {
                    for (int x = 0; x < cols; x++)
                    {
                        clearcell(&cells[y * cols + x]);
                    }
                }
            }
        }
        break;
    }
    case 'l':
    {
        // 1049 l switches back to the Main Buffer and restores cursor
        if (csiseq.prefix == '?' && csiseq.params[0] == 1049)
        {
            if (alt_buffer_active)
            {
                alt_buffer_active = false;
                cells = main_cells;    // Swap the lens back to the Main Buffer
                handlealtcursor(true); // Restore original cursor, scroll, and head positions
            }
        }
        break;
    }
    case 'c':
    {
        if (csiseq.params[0] == 0)
        {
            termwrite("\033[?6c", strlen("\033[?6c"), false);
        }
        break;
    }
    }
}

void handlecodepoint(uint32_t codepoint)
{
    bool isctrl = iscontrol(codepoint);

    if (isctrl)
    {
        if (iscontrolc1(codepoint))
            return;

        handlectrl(codepoint);
        if (escflags == 0)
        {
            mostrecentcodepoint = 0;
        }
        return;
    }
    else if (lf_flag_exists(&escflags, ESC_STATE_ON_ESC))
    {
        if (lf_flag_exists(&escflags, ESC_STATE_CSI))
        {
            csiseq.buf[csiseq.len++] = codepoint;
            if ((0x40 <= codepoint && codepoint <= 0x7E) || csiseq.len >= sizeof(csiseq.buf) - 1)
            {
                escflags = 0;
                parsecsi();
                handlecsi(); // Executing the parsed CSI commands
            }
            return;
        }
        else if (lf_flag_exists(&escflags, ESC_STATE_UTF8))
        {
            // handleutf8
            return;
        }
        else if (lf_flag_exists(&escflags, ESC_STATE_ALTCHARSET))
        {
            escflags = 0; // Prevent freeze
            return;
        }
        else if (lf_flag_exists(&escflags, ESC_STATE_TEST))
        {
            escflags = 0; // Prevent freeze
            return;
        }
        else if (lf_flag_exists(&escflags, ESC_STATE_STR))
        {
            if (codepoint == '\a' || codepoint == '\\')
                escflags = 0; // Break out of string
            return;
        }
        else
        {
            if (handleescseq(codepoint))
                return;
        }
        escflags = 0;
        return;
    }

    // Using proper bitwise flag checking
    if (lf_flag_exists(&cursorstate, CUR_STATE_ONWRAP))
    {
        newline(true);
    }

    if (cursor.x + 1 > cols)
    {
        if (lf_flag_exists(&termflags, TERM_MODE_AUTO_WRAP))
        {
            newline(true);
        }
        else
        {
            moveto(cols - 1, cursor.y);
        }
    }
    setcell(cursor.x, cursor.y, codepoint);
    mostrecentcodepoint = codepoint;
    if (cursor.x + 1 < cols)
    {
        moveto(cursor.x + 1, cursor.y);
    }
    else
    {
        cursorstate |= CUR_STATE_ONWRAP;
    }
}

int32_t utf8decode(const char *s, uint32_t *out_cp)
{
    unsigned char c = s[0];

    if (c < 0x80)
    {
        *out_cp = c;
        return 1;
    }
    else if ((c >> 5) == 0x6)
    {
        *out_cp = ((c & 0x1F) << 6) | (s[1] & 0x3F);
        return 2;
    }
    else if ((c >> 4) == 0xE)
    {
        *out_cp = ((c & 0x0F) << 12) | ((s[1] & 0x3F) << 6) | (s[2] & 0x3F);
        return 3;
    }
    else if ((c >> 3) == 0x1E)
    {
        *out_cp = ((c & 0x07) << 18) | ((s[1] & 0x3F) << 12) |
                  ((s[2] & 0x3F) << 6) | (s[3] & 0x3F);
        return 4;
    }

    return -1; // Invalid UTF-8
}

int32_t utf8encode(uint32_t codepoint, char *out)
{
    if (codepoint <= 0x7F)
    {
        out[0] = codepoint;
        return 1;
    }
    else if (codepoint <= 0x7FF)
    {
        out[0] = 0xC0 | (codepoint >> 6);
        out[1] = 0x80 | (codepoint & 0x3F);
        return 2;
    }
    else if (codepoint <= 0xFFFF)
    {
        out[0] = 0xE0 | (codepoint >> 12);
        out[1] = 0x80 | ((codepoint >> 6) & 0x3F);
        out[2] = 0x80 | (codepoint & 0x3F);
        return 3;
    }
    else if (codepoint <= 0x10FFFF)
    {
        out[0] = 0xF0 | (codepoint >> 18);
        out[1] = 0x80 | ((codepoint >> 12) & 0x3F);
        out[2] = 0x80 | ((codepoint >> 6) & 0x3F);
        out[3] = 0x80 | (codepoint & 0x3F);
        return 4;
    }

    return 0;
}

Cell *getphysrow(int32_t logicalrow)
{
    int32_t physrowidx = (head + logicalrow) % MAX_ROWS;
    return &cells[physrowidx * cols];
}

void clearcell(Cell *cell)
{
    cell->codepoint = ' ';
}

void scrollup(int32_t start, int32_t nscrolls)
{
    for (uint32_t i = 0; i <= scrollbottom - start - nscrolls; i++)
    {
        Cell *src = getphysrow(start + nscrolls + i);
        Cell *dest = getphysrow(start + i);
        memcpy(dest, src, sizeof(Cell) * cols);
    }

    for (uint32_t i = scrollbottom - nscrolls + 1; i <= scrollbottom; i++)
    {
        Cell *row = getphysrow(i);
        for (uint32_t x = 0; x < cols; x++)
        {
            clearcell(&row[x]);
        }
    }
}

void scrolldown(int32_t start, int32_t nscrolls)
{
    for (int32_t i = scrollbottom - start - nscrolls; i >= 0; i--)
    {
        Cell *src = getphysrow(start + i);
        Cell *dest = getphysrow(start + nscrolls + i);
        memcpy(dest, src, sizeof(Cell) * cols);
    }

    for (uint32_t i = start; i <= start + nscrolls; i++)
    {
        Cell *row = getphysrow(i);
        for (uint32_t x = 0; x < cols; x++)
        {
            clearcell(&row[x]);
        }
    }
}

RnTextProps rendertext(RnState *state,
                       const char *text,
                       RnFont *font,
                       vec2s pos,
                       RnColor color,
                       bool render)
{

    // Get the harfbuzz text information for the string
    RnHarfbuzzText *hb_text = rn_hb_text_from_str(state, *font, text);

    // Retrieve highest bearing if
    // it was not retrived yet.
    hb_text->highest_bearing = font->size;

    vec2s start_pos = (vec2s){.x = pos.x, .y = pos.y};

    // New line characters
    const int32_t line_feed = 0x000A;
    const int32_t carriage_return = 0x000D;
    const int32_t line_seperator = 0x2028;
    const int32_t paragraph_seperator = 0x2029;

    float textheight = 0;

    float scale = 1.0f;
    if (font->selected_strike_size)
        scale = ((float)font->size / (float)font->selected_strike_size);

    // OPTIMIZATION 3: Pre-calculate the division multiplier to save CPU cycles
    float scale_multiplier = scale / 64.0f;

    for (unsigned int i = 0; i < hb_text->glyph_count; i++)
    {
        // Get the glyph from the glyph index
        RnGlyph glyph = rn_glyph_from_codepoint(
            state, font,
            hb_text->glyph_info[i].codepoint);

        uint32_t text_length = strlen(text);
        uint32_t codepoint = rn_utf8_to_codepoint(text, hb_text->glyph_info[i].cluster, text_length);
        // Check if the unicode codepoint is a new line and advance
        // to the next line if so
        if (codepoint == line_feed || codepoint == carriage_return ||
            codepoint == line_seperator || codepoint == paragraph_seperator)
        {
            float font_height = font->face->size->metrics.height / 64.0f;
            pos.x = start_pos.x;
            pos.y += font_height;
            textheight += font_height;
            continue;
        }

        // Advance the x position by the tab width if
        // we iterate a tab character
        if (codepoint == '\t')
        {
            pos.x += font->tab_w * font->space_w;
            continue;
        }

        // If the glyph is not within the font, dont render it
        if (!hb_text->glyph_info[i].codepoint)
        {
            continue;
        }

        // Use the pre-calculated multiplier instead of performing division per-character
        float x_advance = hb_text->glyph_pos[i].x_advance * scale_multiplier;
        float y_advance = hb_text->glyph_pos[i].y_advance * scale_multiplier;
        float x_offset = hb_text->glyph_pos[i].x_offset * scale_multiplier;
        float y_offset = hb_text->glyph_pos[i].y_offset * scale_multiplier;

        vec2s glyph_pos = {
            pos.x + x_offset,
            pos.y + hb_text->highest_bearing - y_offset};

        // Render the glyph
        if (render)
        {
            rn_glyph_render(state, glyph, *font, glyph_pos, color);
        }

        if (glyph.height > textheight)
        {
            textheight = glyph.height;
        }

        // Advance to the next glyph
        pos.x += x_advance;
        pos.y += y_advance;
    }

    return (RnTextProps){
        .width = pos.x - start_pos.x,
        .height = textheight,
        .paragraph_pos = pos};
}

void renderrows()
{
    float char_width = 12.0f;
    float line_height = font.font->line_h;

    // 1. Draw the Cursor Visualizer
    // We draw this first so the white text renders cleanly on top of it.
    if (!lf_flag_exists(&termflags, TERM_MODE_HIDE_CURSOR))
    {
        float cursor_px_x = cursor.x * char_width;
        float cursor_px_y = cursor.y * line_height;

        // Draw a solid gray block at the active cell.
        // We use 150.0f for RGB to get a neutral gray that contrasts with black and white.
        rn_rect_render_base_types(
            ui->render_state,
            cursor_px_x,
            cursor_px_y,
            char_width,
            line_height,
            0.0f,   // Rotation
            150.0f, // R
            150.0f, // G
            150.0f, // B
            255.0f  // Alpha (fully opaque)
        );
    }

    // 2. Draw the Text Grid (Highly Optimized)
    float y = 0.0f;
    for (uint32_t i = 0; i < rows; i++)
    {
        // OPTIMIZATION 1: Fast Stack Allocation (Zero heap fragmentation)
        char row[(cols * 4) + 1];
        char *rowptr = row;

        // OPTIMIZATION 2: Skip Dead Space
        int32_t last_char = cols - 1;
        while (last_char >= 0 && (cells[i * cols + last_char].codepoint == ' ' || cells[i * cols + last_char].codepoint == 0))
        {
            last_char--;
        }

        // Only run the UTF-8 encoder up to the last visible character
        for (int32_t j = 0; j <= last_char; j++)
        {
            rowptr += utf8encode(cells[i * cols + j].codepoint, rowptr);
        }
        *rowptr = '\0';

        // Only call the heavy Harfbuzz/Runara renderer if there is actually text to draw
        if (last_char >= 0)
        {
            rendertext(ui->render_state, row, font.font, (vec2s){.x = 0, .y = y}, RN_WHITE, true);
        }

        y += line_height;
    }
}

void termnextevent(lf_ui_state_t *ui)
{
    float cur_time = lf_ui_core_get_elapsed_time();
    ui->delta_time = cur_time - ui->_last_time;
    ui->_last_time = cur_time;

    bool rendered = lf_windowing_get_current_event() == LF_EVENT_WINDOW_REFRESH;

    lf_ui_core_shape_widgets_if_needed(ui, ui->root, false);

    lf_win_make_gl_context(ui->win);
    vec2s winsize = lf_win_get_size(ui->win);
    ui->render_clear_color_area(
        lf_color_from_hex(0x1a1a1a),
        LF_SCALE_CONTAINER(winsize.x, winsize.y), winsize.y);

    ui->render_begin(ui->render_state);
    renderrows();
    ui->render_end(ui->render_state);

    lf_win_swap_buffers(ui->win);

    ui->needs_render = false;
    rendered = true;

    lf_windowing_update();
}

static size_t readfrompty(void);

void writetopty(const char *buf, size_t len)
{
    fd_set writeset, readset;
    uint32_t writelimit = 256;

    while (len > 0)
    {
        FD_ZERO(&writeset);
        FD_ZERO(&readset);
        FD_SET(masterfd, &writeset);
        FD_SET(masterfd, &readset);

        if (pselect(masterfd + 1, &readset, &writeset, NULL, NULL, NULL) < 0)
        {
            if (errno == EINTR)
                continue;
            fprintf(stderr, "pselect() failed: %s\n", strerror(errno));
            exit(1);
        }

        if (FD_ISSET(masterfd, &writeset))
        {
            int32_t nwritten = write(masterfd, buf, MIN(len, writelimit));
            if (nwritten < 0)
            {
                if (errno == EINTR || errno == EAGAIN)
                    continue;
                fprintf(stderr, "write() failed: %s\n", strerror(errno));
                exit(1);
            }
            if (nwritten >= len)
                break;
            if (nwritten < writelimit)
            {
                writelimit = readfrompty();
            }
            len -= nwritten;
            buf += nwritten;
        }
        if (FD_ISSET(masterfd, &readset))
        {
            writelimit = readfrompty();
        }
    }
}

uint32_t
termhandlecharstream(const char *buf, uint32_t len)
{
    uint32_t n = 0;
    while (n < len)
    {
        int32_t charlen = 1;
        uint32_t codepoint;
        if (lf_flag_exists(&termflags, TERM_MODE_UTF8))
        {
            charlen = utf8decode(buf + n, &codepoint);
        }
        else
        {
            codepoint = buf[n] & 0xFF;
        }
        handlecodepoint(codepoint);
        n += charlen;
    }
    return n;
}

void termwrite(const char *buf, size_t len, bool mayecho)
{
    if (mayecho && lf_flag_exists(&termflags, TERM_MODE_ECHO))
    {
        termhandlecharstream(buf, len);
    }
    if (!lf_flag_exists(&termflags, TERM_MODE_CR_AND_LF))
    {
        writetopty(buf, len);
    }

    while (len > 0)
    {
        if (*buf == '\r')
        {
            // If the current character is a carriage return,
            writetopty("\r\n", 1);
            buf++;
            len--;
        }
        else
        {
            // Find the next carriage return or end of buffer
            char *next_cr = memchr(buf, '\r', len);
            if (!next_cr)
            {
                next_cr = (char *)buf + len;
            }

            // Write the characters till the next CR
            writetopty(buf, next_cr - buf);

            // Decrement length
            len -= next_cr - buf;
            // Advance buffeer to the next carriage return
            buf = next_cr;
        }
    }
}

size_t readfrompty(void)
{
    static char buf[SHRT_MAX];
    static uint32_t buflen = 0;

    int32_t nbytes = read(masterfd, buf + buflen, sizeof(buf) - buflen);

    // MINIMAL FIX: If bash exits, read returns -1 (or 0). Stop here.
    if (nbytes <= 0)
    {
        return 0;
    }

    buflen += nbytes;

    uint32_t iter = 0;
    while (iter < buflen)
    {
        uint32_t codepoint;
        int32_t len = utf8decode(&buf[iter], &codepoint);
        if (len == -1 || len > buflen)
            break;
        // printf("%i\n", codepoint);
        handlecodepoint(codepoint);
        iter += len;
    }

    if (iter < buflen)
    {
        memmove(buf, buf + iter, buflen - iter);
    }

    buflen -= iter;

    return nbytes;
}

void charcb(lf_ui_state_t *ui, lf_window_t win, char *utf8, uint32_t utf8len)
{
    (void)ui;
    (void)win;

    // STRICT FIX: Only block Backspace/Delete (127 and 8).
    // This allows Enter (\r), Ctrl+C, Ctrl+D, and Ctrl+L to pass through to the PTY.
    if (utf8len == 1 && (utf8[0] == '\x7f' || utf8[0] == '\b'))
    {
        return;
    }

    termwrite(utf8, utf8len, false);
}

/* * Hardware Key Callback */
void keycb(lf_ui_state_t *ui, lf_window_t win, int32_t key, int32_t scancode, int32_t action, int32_t mods)
{
    (void)ui;
    (void)win;
    (void)scancode;
    (void)mods;

    if (action == LF_KEY_ACTION_RELEASE)
    {
        return;
    }

    char seq[8] = {0};
    int seqlen = 0;

    // Translate hardware keys to standard VT100/ANSI control sequences
    if (key == KeyBackspace)
    {
        seq[0] = '\x7f';
        seqlen = 1;
    }
    else if (key == KeyDelete)
    {
        strcpy(seq, "\033[3~");
        seqlen = 4;
    }
    else if (key == KeyUp)
    {
        strcpy(seq, "\033[A");
        seqlen = 3;
    }
    else if (key == KeyDown)
    {
        strcpy(seq, "\033[B");
        seqlen = 3;
    }
    else if (key == KeyRight)
    {
        strcpy(seq, "\033[C");
        seqlen = 3;
    }
    else if (key == KeyLeft)
    {
        strcpy(seq, "\033[D");
        seqlen = 3;
    }
    else if (key == KeyTab)
    {
        seq[0] = '\t';
        seqlen = 1;
    }
    /* --- FOR F8 --- */
    else if (key == KeyF8)
    {
        strcpy(seq, "\033[19~");
        seqlen = 5;
    }
    // Push the translated sequence directly into the PTY master file descriptor
    if (seqlen > 0)
    {
        writetopty(seq, seqlen);
    }
}

void update_terminal_geometry(uint32_t win_width, uint32_t win_height)
{
    // Get the exact line height directly from the rendering engine.
    float line_height = (font.font != NULL) ? font.font->line_h : 25.0f;
    float char_width = 12.0f;

    // Prevent division by zero if window is minimized
    if (win_width < char_width)
        win_width = char_width;
    if (win_height < line_height)
        win_height = line_height;

    uint32_t new_cols = win_width / char_width;
    uint32_t new_rows = (win_height - 5) / line_height;

    // Only hit the RAM if the grid size actually changed
    if (new_cols != cols || new_rows != rows)
    {
        cols = new_cols;
        rows = new_rows;

        // Dynamically resize BOTH memory blocks AND the tabs array
        main_cells = realloc(main_cells, sizeof(Cell) * rows * cols);
        alt_cells = realloc(alt_cells, sizeof(Cell) * rows * cols);
        tabs = realloc(tabs, sizeof(uint32_t) * cols); // <--- THE FIX

        // Wipe the newly sized grids clean to prevent random garbage characters
        memset(main_cells, 0, sizeof(Cell) * rows * cols);
        memset(alt_cells, 0, sizeof(Cell) * rows * cols);

        // Point the active lens to whichever buffer is currently in use
        cells = alt_buffer_active ? alt_cells : main_cells;

        // Rebuild the tab stops for the new width
        for (uint32_t i = 0; i < cols; i++)
        {
            tabs[i] = (i % 4 == 0) ? 1 : 0;
        }

        // Reset boundaries to match the new height
        scrolltop = 0;
        scrollbottom = rows - 1;

        // Clamp the cursor so it doesn't get trapped outside the new window
        if (cursor.x >= cols)
            cursor.x = cols - 1;
        if (cursor.y >= rows)
            cursor.y = rows - 1;
    }

    struct winsize ws = {
        .ws_row = (unsigned short)rows,
        .ws_col = (unsigned short)cols,
        .ws_xpixel = (unsigned short)win_width,
        .ws_ypixel = (unsigned short)win_height};

    ioctl(masterfd, TIOCSWINSZ, &ws);
}

/* * Window Resize Callback */
void resizecb(lf_ui_state_t *ui, lf_window_t win, uint32_t width, uint32_t height)
{
    (void)ui;
    (void)width;
    (void)height;

    // Fetch the absolute exact size directly from the engine to guarantee accuracy
    vec2s winsize = lf_win_get_size(win);

    // Recalculate grid, realloc memory, and update the PTY
    update_terminal_geometry((uint32_t)winsize.x, (uint32_t)winsize.y);

    // Force an immediate frame render so it doesn't wait for a keypress
    ui->needs_render = true;
}

int main(void)
{
    if (forkpty(&masterfd, NULL, NULL, NULL) == 0)
    {
        execlp("/usr/bin/bash", "bash", NULL);
        perror("execlp");
        exit(1);
    }

    lf_flag_set(&termflags, TERM_MODE_UTF8 | TERM_MODE_AUTO_WRAP);
    lf_windowing_init();

    lf_window_t win = lf_ui_core_create_window(1280, 720, "Terminator");
    ui = lf_ui_core_init(win);
    font = lf_asset_manager_request_font(ui, "JetBrains Mono Nerd Font", LF_FONT_STYLE_REGULAR, 20);

    // Get the ACTUAL window size dictated by the OS/Window Manager
    vec2s initial_size = lf_win_get_size(win);

    // This single call now handles math, memory allocation, and PTY notification.
    update_terminal_geometry((uint32_t)initial_size.x, (uint32_t)initial_size.y);

    // Register Event Callbacks
    lf_win_set_typing_char_cb(win, charcb);
    lf_win_set_key_cb(win, keycb);
    lf_win_set_resize_cb(win, resizecb);

    fd_set fdset;
    int32_t x11fd = ConnectionNumber(lf_win_get_x11_display());
    bool first_time = true;

    while (ui->running)
    {
        FD_ZERO(&fdset);
        FD_SET(masterfd, &fdset);
        FD_SET(x11fd, &fdset);

        if (first_time)
        {
            termnextevent(ui);
            first_time = false;
        }

        select(MAX(masterfd, x11fd) + 1, &fdset, NULL, NULL, NULL);

        bool needs_render = false;

        if (FD_ISSET(masterfd, &fdset))
        {
            // MINIMAL FIX: If the shell died (returned 0), break the loop cleanly.
            if (readfrompty() == 0)
            {
                break;
            }
            ui->needs_render = true;
            termnextevent(ui);
        }

        if (FD_ISSET(x11fd, &fdset))
        {
            lf_windowing_next_event();

            lf_event_type_t curevent = lf_windowing_get_current_event();

            if (curevent == LF_EVENT_WINDOW_CLOSE)
            {
                break;
            }
            // LF_EVENT_WINDOW_RESIZE is removed here because resizecb handles it natively
            else if (curevent == LF_EVENT_KEY_PRESS || curevent == LF_EVENT_TYPING_CHAR ||
                     curevent == LF_EVENT_WINDOW_REFRESH)
            {
                needs_render = true;
            }
        }
        if (needs_render)
            termnextevent(ui);
    }

    printf("Hello World !!\n");
    return EXIT_SUCCESS;
}