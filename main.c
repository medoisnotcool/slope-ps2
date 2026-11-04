/*
 * SLOPE - PlayStation 2 port
 * Endless 3D runner: steer the ball with the D-pad (left / right),
 * dodge the red blocks, avoid holes and the edges of the track.
 *
 * Built with PS2SDK + gsKit (no external assets needed, everything is
 * drawn with coloured gouraud triangles).
 *
 * Controls
 *   D-pad LEFT / RIGHT   steer
 *   START or X           start / retry
 */

#include <tamtypes.h>
#include <kernel.h>
#include <sifrpc.h>
#include <loadfile.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <gsKit.h>
#include <dmaKit.h>
#include <libpad.h>

/* ------------------------------------------------------------------ */
/* constants                                                           */
/* ------------------------------------------------------------------ */
#define ROWLEN      3.0f      /* length of one track row                */
#define NROWS       64        /* ring buffer of track rows (power of 2) */
#define VIEW_ROWS   46        /* how many rows ahead are drawn          */
#define BALL_R      0.5f
#define TILE_T      0.7f      /* thickness of the track slab            */
#define NEAR_Z      0.6f
#define GUARD       900.0f    /* 2D clip guard band (GS coord range)    */
#define FOG_NEAR    28.0f
#define FOG_FAR     128.0f
#define CAM_H       3.6f
#define CAM_BACK    6.5f
#define PITCH       0.215f

enum { ST_TITLE = 0, ST_PLAY = 1, ST_DEAD = 2 };

/* ------------------------------------------------------------------ */
/* globals                                                             */
/* ------------------------------------------------------------------ */
static GSGLOBAL *gs;
static float SW = 640.0f, SH = 448.0f;
static float FOCAL = 544.0f;
static float DT = 1.0f / 60.0f;

static float cam_x, cam_y, cam_z, cp, sp;
static float cam_shake;
static float horizon_y;

typedef struct { float v[6]; } Vtx;      /* x y z r g b */

typedef struct {
    int   id;
    int   ok;
    float l, r;
    int   hole;
    float hl, hr;
    int   nobs;
    float ox[3], ow[3], oh[3], oz0[3], oz1[3];
} Row;

static Row rows[NROWS];
#define ROW(n) (&rows[(n) & (NROWS - 1)])

typedef struct { float x, y, z, vx, vy; int fell; } Ball;
static Ball ball;

static int   state = ST_TITLE;
static float speed = 14.0f;
static float t_play = 0.0f;
static float dead_t = 0.0f;
static int   score = 0, best = 0;
static int   frame = 0;
static int   crashed = 0;

/* world generator state */
static int   demo_mode;
static int   gen_next;
static float g_center, g_turn, g_turn_t, g_width;
static int   g_hole_left;
static float g_hl, g_hr;
static int   g_last_obs;

/* stars */
#define NSTARS 48
static float star_x[NSTARS], star_y[NSTARS];
static int   star_b[NSTARS];

/* ------------------------------------------------------------------ */
/* palette                                                             */
/* ------------------------------------------------------------------ */
static const float C_SKY_TOP[3]  = {  4.0f,   4.0f,  20.0f };
static const float C_HORIZON[3]  = { 78.0f,  36.0f, 124.0f };
static const float C_VOID_BOT[3] = {  6.0f,   6.0f,  22.0f };
static const float C_TOP_A[3]    = { 30.0f,  44.0f,  92.0f };
static const float C_TOP_B[3]    = { 24.0f,  35.0f,  76.0f };
static const float C_FRONT[3]    = { 16.0f,  22.0f,  52.0f };
static const float C_WALL[3]     = { 10.0f,  14.0f,  36.0f };
static const float C_NEON[3]     = { 70.0f, 255.0f, 225.0f };
static const float C_OB_FRONT[3] = { 200.0f,  28.0f,  44.0f };
static const float C_OB_SIDE[3]  = { 130.0f,  16.0f,  30.0f };
static const float C_OB_TOP[3]   = { 255.0f,  96.0f, 104.0f };

/* ------------------------------------------------------------------ */
/* small helpers                                                       */
/* ------------------------------------------------------------------ */
static float clampf(float v, float a, float b) { return v < a ? a : (v > b ? b : v); }

static unsigned int rng_s = 2463534242u;
static unsigned int rnd(void)
{
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 17;
    rng_s ^= rng_s << 5;
    return rng_s;
}
static float rndf(float a, float b) { return a + (b - a) * ((rnd() & 0xFFFF) / 65535.0f); }

static u64 col64(float r, float g, float b, int a)
{
    int ri = (int)clampf(r, 0.0f, 255.0f);
    int gi = (int)clampf(g, 0.0f, 255.0f);
    int bi = (int)clampf(b, 0.0f, 255.0f);
    if (a < 0) a = 0;
    if (a > 0x80) a = 0x80;
    return GS_SETREG_RGBAQ(ri, gi, bi, a, 0x00);
}

static void tri2(float x0, float y0, u64 c0, float x1, float y1, u64 c1, float x2, float y2, u64 c2)
{
    gsKit_prim_triangle_gouraud_3d(gs, x0, y0, 0, x1, y1, 0, x2, y2, 0, c0, c1, c2);
}

static void rect(float x0, float y0, float x1, float y1, u64 c)
{
    gsKit_prim_sprite(gs, x0, y0, x1, y1, 0, c);
}

/* ------------------------------------------------------------------ */
/* bitmap font (5x7)                                                   */
/* ------------------------------------------------------------------ */
static const unsigned char FONT[40][7] = {
    {0x0E,0x11,0x13,0x15,0x19,0x11,0x0E}, /* 0 */
    {0x04,0x0C,0x04,0x04,0x04,0x04,0x0E}, /* 1 */
    {0x0E,0x11,0x01,0x02,0x04,0x08,0x1F}, /* 2 */
    {0x0E,0x11,0x01,0x06,0x01,0x11,0x0E}, /* 3 */
    {0x02,0x06,0x0A,0x12,0x1F,0x02,0x02}, /* 4 */
    {0x1F,0x10,0x1E,0x01,0x01,0x11,0x0E}, /* 5 */
    {0x06,0x08,0x10,0x1E,0x11,0x11,0x0E}, /* 6 */
    {0x1F,0x01,0x02,0x04,0x08,0x08,0x08}, /* 7 */
    {0x0E,0x11,0x11,0x0E,0x11,0x11,0x0E}, /* 8 */
    {0x0E,0x11,0x11,0x0F,0x01,0x02,0x0C}, /* 9 */
    {0x0E,0x11,0x11,0x1F,0x11,0x11,0x11}, /* A */
    {0x1E,0x11,0x11,0x1E,0x11,0x11,0x1E}, /* B */
    {0x0E,0x11,0x10,0x10,0x10,0x11,0x0E}, /* C */
    {0x1E,0x11,0x11,0x11,0x11,0x11,0x1E}, /* D */
    {0x1F,0x10,0x10,0x1E,0x10,0x10,0x1F}, /* E */
    {0x1F,0x10,0x10,0x1E,0x10,0x10,0x10}, /* F */
    {0x0E,0x11,0x10,0x17,0x11,0x11,0x0E}, /* G */
    {0x11,0x11,0x11,0x1F,0x11,0x11,0x11}, /* H */
    {0x0E,0x04,0x04,0x04,0x04,0x04,0x0E}, /* I */
    {0x07,0x02,0x02,0x02,0x02,0x12,0x0C}, /* J */
    {0x11,0x12,0x14,0x18,0x14,0x12,0x11}, /* K */
    {0x10,0x10,0x10,0x10,0x10,0x10,0x1F}, /* L */
    {0x11,0x1B,0x15,0x15,0x11,0x11,0x11}, /* M */
    {0x11,0x19,0x15,0x13,0x11,0x11,0x11}, /* N */
    {0x0E,0x11,0x11,0x11,0x11,0x11,0x0E}, /* O */
    {0x1E,0x11,0x11,0x1E,0x10,0x10,0x10}, /* P */
    {0x0E,0x11,0x11,0x11,0x15,0x12,0x0D}, /* Q */
    {0x1E,0x11,0x11,0x1E,0x14,0x12,0x11}, /* R */
    {0x0F,0x10,0x10,0x0E,0x01,0x01,0x1E}, /* S */
    {0x1F,0x04,0x04,0x04,0x04,0x04,0x04}, /* T */
    {0x11,0x11,0x11,0x11,0x11,0x11,0x0E}, /* U */
    {0x11,0x11,0x11,0x11,0x11,0x0A,0x04}, /* V */
    {0x11,0x11,0x11,0x15,0x15,0x1B,0x11}, /* W */
    {0x11,0x11,0x0A,0x04,0x0A,0x11,0x11}, /* X */
    {0x11,0x11,0x0A,0x04,0x04,0x04,0x04}, /* Y */
    {0x1F,0x01,0x02,0x04,0x08,0x10,0x1F}, /* Z */
    {0x00,0x00,0x00,0x00,0x00,0x00,0x00}, /* space */
    {0x00,0x00,0x00,0x1F,0x00,0x00,0x00}, /* - */
    {0x00,0x04,0x00,0x00,0x00,0x04,0x00}, /* : */
    {0x04,0x04,0x04,0x04,0x04,0x00,0x04}, /* ! */
};

static const unsigned char *glyph(char c)
{
    if (c >= '0' && c <= '9') return FONT[c - '0'];
    if (c >= 'A' && c <= 'Z') return FONT[10 + c - 'A'];
    if (c >= 'a' && c <= 'z') return FONT[10 + c - 'a'];
    if (c == '-') return FONT[37];
    if (c == ':') return FONT[38];
    if (c == '!') return FONT[39];
    return FONT[36];
}

static float text_w(const char *s, float px) { return (float)strlen(s) * 6.0f * px - px; }

static void draw_text(const char *s, float x, float y, float px, u64 col)
{
    for (; *s; s++, x += 6.0f * px) {
        const unsigned char *g = glyph(*s);
        int row, c, e;
        for (row = 0; row < 7; row++) {
            unsigned char bits = g[row];
            c = 0;
            while (c < 5) {
                if (bits & (0x10 >> c)) {
                    e = c;
                    while (e < 5 && (bits & (0x10 >> e))) e++;
                    rect(x + c * px, y + row * px, x + e * px, y + (row + 1) * px, col);
                    c = e;
                } else {
                    c++;
                }
            }
        }
    }
}

static void draw_text_sh(const char *s, float x, float y, float px, u64 col)
{
    draw_text(s, x + px * 0.7f, y + px * 0.7f, px, col64(0, 0, 0, 0x60));
    draw_text(s, x, y, px, col);
}

static void draw_text_c(const char *s, float y, float px, u64 col)
{
    draw_text_sh(s, (SW - text_w(s, px)) * 0.5f, y, px, col);
}

/* ------------------------------------------------------------------ */
/* 3D pipeline: camera transform -> near clip -> project -> fog ->     */
/*              2D guard-band clip -> gouraud triangle fan             */
/* ------------------------------------------------------------------ */
static int clip_poly(const Vtx *in, int n, Vtx *out, int axis, float sign, float val)
{
    int i, k, m = 0;
    for (i = 0; i < n; i++) {
        const Vtx *a = &in[i];
        const Vtx *b = &in[(i + 1) % n];
        float da = sign * (a->v[axis] - val);
        float db = sign * (b->v[axis] - val);
        int ain = da >= 0.0f, bin = db >= 0.0f;
        if (ain) out[m++] = *a;
        if (ain != bin) {
            float t = da / (da - db);
            Vtx c;
            for (k = 0; k < 6; k++) c.v[k] = a->v[k] + (b->v[k] - a->v[k]) * t;
            out[m++] = c;
        }
    }
    return m;
}

static int project(float x, float y, float z, float *sx, float *sy, float *dz)
{
    float dx = x - cam_x, dy = y - cam_y, dzz = z - cam_z;
    float yc = dy * cp + dzz * sp;
    float zc = -dy * sp + dzz * cp;
    if (zc < NEAR_Z) return 0;
    *sx = SW * 0.5f + dx / zc * FOCAL;
    *sy = SH * 0.5f - yc / zc * FOCAL;
    *dz = zc;
    return 1;
}

static void draw_poly(const Vtx *in, int n)
{
    Vtx A[16], B[16];
    int i;

    n = clip_poly(in, n, A, 2, 1.0f, NEAR_Z);
    if (n < 3) return;

    for (i = 0; i < n; i++) {
        float z = A[i].v[2];
        float inv = FOCAL / z;
        float f = clampf((z - FOG_NEAR) / (FOG_FAR - FOG_NEAR), 0.0f, 1.0f);
        A[i].v[0] = SW * 0.5f + A[i].v[0] * inv;
        A[i].v[1] = SH * 0.5f - A[i].v[1] * inv;
        A[i].v[3] += (C_HORIZON[0] - A[i].v[3]) * f;
        A[i].v[4] += (C_HORIZON[1] - A[i].v[4]) * f;
        A[i].v[5] += (C_HORIZON[2] - A[i].v[5]) * f;
    }

    n = clip_poly(A, n, B, 0,  1.0f, -GUARD);          if (n < 3) return;
    n = clip_poly(B, n, A, 0, -1.0f, SW + GUARD);      if (n < 3) return;
    n = clip_poly(A, n, B, 1,  1.0f, -GUARD);          if (n < 3) return;
    n = clip_poly(B, n, A, 1, -1.0f, SH + GUARD);      if (n < 3) return;

    for (i = 1; i + 1 < n; i++) {
        tri2(A[0].v[0], A[0].v[1], col64(A[0].v[3], A[0].v[4], A[0].v[5], 0x80),
             A[i].v[0], A[i].v[1], col64(A[i].v[3], A[i].v[4], A[i].v[5], 0x80),
             A[i + 1].v[0], A[i + 1].v[1], col64(A[i + 1].v[3], A[i + 1].v[4], A[i + 1].v[5], 0x80));
    }
}

static Vtx make_vtx(float x, float y, float z, const float *c)
{
    Vtx o;
    float dx = x - cam_x, dy = y - cam_y, dz = z - cam_z;
    o.v[0] = dx;
    o.v[1] = dy * cp + dz * sp;
    o.v[2] = -dy * sp + dz * cp;
    o.v[3] = c[0]; o.v[4] = c[1]; o.v[5] = c[2];
    return o;
}

static void quad3(float x0, float y0, float z0, float x1, float y1, float z1,
                  float x2, float y2, float z2, float x3, float y3, float z3, const float *c)
{
    Vtx p[4];
    p[0] = make_vtx(x0, y0, z0, c);
    p[1] = make_vtx(x1, y1, z1, c);
    p[2] = make_vtx(x2, y2, z2, c);
    p[3] = make_vtx(x3, y3, z3, c);
    draw_poly(p, 4);
}

/* ------------------------------------------------------------------ */
/* track generation                                                    */
/* ------------------------------------------------------------------ */
static int corridor_ok(const Row *R)
{
    int idx[3], i, j, t;
    float prev, best = 0.0f;
    for (i = 0; i < R->nobs; i++) idx[i] = i;
    for (i = 0; i < R->nobs; i++)
        for (j = i + 1; j < R->nobs; j++)
            if (R->ox[idx[j]] < R->ox[idx[i]]) { t = idx[i]; idx[i] = idx[j]; idx[j] = t; }
    prev = R->l;
    for (i = 0; i < R->nobs; i++) {
        int k = idx[i];
        float lo = R->ox[k] - R->ow[k] * 0.5f;
        float hi = R->ox[k] + R->ow[k] * 0.5f;
        if (lo - prev > best) best = lo - prev;
        if (hi > prev) prev = hi;
    }
    if (R->r - prev > best) best = R->r - prev;
    return best >= 2.0f;
}

static void gen_row(int n)
{
    Row *R = ROW(n);
    float zpos = n * ROWLEN;
    float d = zpos / 1800.0f;
    float wt;
    int can_event, i, cnt;

    if (d > 1.0f) d = 1.0f;
    wt = 9.0f - 4.0f * d;

    memset(R, 0, sizeof(Row));
    R->id = n;
    R->ok = 1;

    if (n >= 8) {
        if ((rnd() % 6) == 0) g_turn_t = rndf(-1.0f, 1.0f) * (0.20f + 0.22f * d);
        if (g_center >  8.0f) g_turn_t = -0.25f;
        if (g_center < -8.0f) g_turn_t =  0.25f;
        g_turn += (g_turn_t - g_turn) * 0.3f;
        g_center += g_turn;
    }
    g_width += (wt - g_width) * 0.15f;
    R->l = g_center - g_width * 0.5f;
    R->r = g_center + g_width * 0.5f;

    can_event = (!demo_mode && n >= 14);

    if (g_hole_left > 0) {
        R->hole = 1;
        R->hl = g_hl;
        R->hr = g_hr;
        g_hole_left--;
        g_last_obs = n;
    } else if (can_event && (n - g_last_obs) >= 5 && (rnd() % (unsigned)(12 - (int)(5.0f * d))) == 0) {
        float hw = rndf(2.0f, 3.0f);
        g_hl = rndf(R->l, R->r - hw);
        g_hr = g_hl + hw;
        g_hole_left = (int)(rnd() % 3);
        R->hole = 1;
        R->hl = g_hl;
        R->hr = g_hr;
        g_last_obs = n;
    } else if (can_event && (n - g_last_obs) >= (6 - (int)(3.0f * d)) && (rnd() % 3) != 0) {
        cnt = 1 + ((d > 0.3f && (rnd() & 1)) ? 1 : 0) + ((d > 0.65f && (rnd() & 1)) ? 1 : 0);
        for (i = 0; i < cnt; i++) {
            float w = rndf(1.1f, 2.0f);
            float cx, h;
            int k, bad = 0;
            if (g_width < w + 2.6f) continue;
            cx = rndf(R->l + w * 0.5f, R->r - w * 0.5f);
            h = rndf(1.1f, 1.7f);
            for (k = 0; k < R->nobs; k++)
                if (fabsf(cx - R->ox[k]) < (w + R->ow[k]) * 0.5f + 0.25f) bad = 1;
            if (bad) continue;
            k = R->nobs;
            R->ox[k] = cx; R->ow[k] = w; R->oh[k] = h;
            R->oz0[k] = zpos + 0.9f;
            R->oz1[k] = zpos + 2.1f;
            R->nobs++;
            if (!corridor_ok(R)) R->nobs--;
        }
        if (R->nobs > 0) g_last_obs = n;
    }

    if (R->hole) {
        float lf = R->hl - R->l, rf = R->r - R->hr;
        if (lf < 1.8f && rf < 1.8f) {
            float w = R->hr - R->hl;
            R->hr = R->r - 2.0f;
            R->hl = R->hr - w;
            if (R->hl < R->l) R->hl = R->l;
            g_hl = R->hl;
            g_hr = R->hr;
        }
    }
}

static void gen_ahead(int brow)
{
    while (gen_next < brow + VIEW_ROWS + 4) gen_row(gen_next++);
}

static void world_reset(int demo)
{
    int i;
    for (i = 0; i < NROWS; i++) { memset(&rows[i], 0, sizeof(Row)); rows[i].id = -1; }
    demo_mode = demo;
    g_center = 0.0f; g_turn = 0.0f; g_turn_t = 0.0f; g_width = 9.0f;
    g_hole_left = 0; g_hl = g_hr = 0.0f; g_last_obs = -100;
    gen_next = 0;
    while (gen_next < NROWS - 12) gen_row(gen_next++);
}

static int floor_in_row(int n, float x)
{
    Row *R;
    if (n < 0) return 0;
    R = ROW(n);
    if (R->id != n || !R->ok) return 0;
    if (x < R->l || x > R->r) return 0;
    if (R->hole && x > R->hl && x < R->hr) return 0;
    return 1;
}

static int floor_at(float x, float z) { return floor_in_row((int)floorf(z / ROWLEN), x); }

static int hit_obstacle(void)
{
    int n0 = (int)floorf((ball.z - BALL_R) / ROWLEN);
    int n1 = (int)floorf((ball.z + BALL_R) / ROWLEN);
    int n, k;
    float rr = BALL_R * 0.85f;
    for (n = n0; n <= n1; n++) {
        Row *R;
        if (n < 0) continue;
        R = ROW(n);
        if (R->id != n || !R->ok) continue;
        for (k = 0; k < R->nobs; k++) {
            if (ball.z + rr > R->oz0[k] && ball.z - rr < R->oz1[k] &&
                fabsf(ball.x - R->ox[k]) < R->ow[k] * 0.5f + rr &&
                (ball.y - BALL_R) < R->oh[k])
                return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* game logic                                                          */
/* ------------------------------------------------------------------ */
static void camera_snap(void)
{
    cam_x = ball.x * 0.85f;
    cam_y = CAM_H;
    cam_z = ball.z - CAM_BACK;
}

static void camera_update(float dt)
{
    float tx = ball.x * 0.85f;
    cam_x += (tx - cam_x) * clampf(7.0f * dt, 0.0f, 1.0f);
    cam_y = CAM_H + clampf(ball.y - BALL_R, -20.0f, 0.0f) * 0.6f;
    cam_z = ball.z - CAM_BACK;
    if (cam_shake > 0.0f) {
        cam_x += rndf(-1.0f, 1.0f) * cam_shake * 0.35f;
        cam_y += rndf(-1.0f, 1.0f) * cam_shake * 0.35f;
        cam_shake -= dt * 1.6f;
        if (cam_shake < 0.0f) cam_shake = 0.0f;
    }
    cp = cosf(PITCH);
    sp = sinf(PITCH);
}

static void start_title(void)
{
    world_reset(1);
    ball.x = 0.0f; ball.y = BALL_R; ball.z = ROWLEN * 1.5f;
    ball.vx = ball.vy = 0.0f; ball.fell = 0;
    state = ST_TITLE;
    speed = 16.0f;
    cam_shake = 0.0f;
    camera_snap();
}

static void start_game(void)
{
    rng_s ^= (unsigned)(frame * 2654435761u) | 1u;
    world_reset(0);
    ball.x = 0.0f; ball.y = BALL_R; ball.z = ROWLEN * 1.5f;
    ball.vx = ball.vy = 0.0f; ball.fell = 0;
    speed = 14.0f;
    t_play = 0.0f;
    score = 0;
    crashed = 0;
    dead_t = 0.0f;
    cam_shake = 0.0f;
    state = ST_PLAY;
    camera_snap();
}

static void die(int crash)
{
    state = ST_DEAD;
    crashed = crash;
    dead_t = 0.0f;
    if (crash) cam_shake = 1.0f;
    if (score > best) best = score;
}

static void update_title(float dt)
{
    int brow;
    Row *R;
    float tx = 0.0f;
    ball.z += 16.0f * dt;
    brow = (int)floorf(ball.z / ROWLEN);
    gen_ahead(brow);
    R = ROW(brow + 2);
    if (R->id == brow + 2) tx = (R->l + R->r) * 0.5f;
    ball.x += (tx - ball.x) * clampf(3.0f * dt, 0.0f, 1.0f);
    ball.y = BALL_R;
    camera_update(dt);
}

static void update_play(float dt, u32 pad)
{
    float dir = 0.0f, vmax, target, acc;
    int s, steps = 2;
    float h = dt / steps;

    t_play += dt;
    speed = clampf(14.0f + 0.45f * t_play, 14.0f, 60.0f);

    if (pad & PAD_LEFT)  dir -= 1.0f;
    if (pad & PAD_RIGHT) dir += 1.0f;

    if (!ball.fell) {
        vmax = 9.0f + speed * 0.12f;
        target = dir * vmax;
        acc = 70.0f * dt;
        ball.vx += clampf(target - ball.vx, -acc, acc);
    }

    for (s = 0; s < steps; s++) {
        ball.x += ball.vx * h;
        ball.z += speed * h;

        if (!ball.fell) {
            if (!floor_at(ball.x, ball.z)) {
                ball.fell = 1;
                ball.vy = 0.0f;
            } else if (hit_obstacle()) {
                score = (int)((ball.z - ROWLEN * 1.5f) * 0.25f);
                die(1);
                break;
            }
        } else {
            ball.vy -= 34.0f * h;
            ball.y += ball.vy * h;
            if (ball.y < -3.5f) {
                score = (int)((ball.z - ROWLEN * 1.5f) * 0.25f);
                die(0);
                break;
            }
        }
    }

    if (state == ST_PLAY) score = (int)((ball.z - ROWLEN * 1.5f) * 0.25f);
    gen_ahead((int)floorf(ball.z / ROWLEN));
    camera_update(dt);
}

static void update_dead(float dt)
{
    dead_t += dt;
    if (!crashed) {
        /* keep the fall going a little for looks */
    }
    camera_update(dt);
}

/* ------------------------------------------------------------------ */
/* rendering                                                           */
/* ------------------------------------------------------------------ */
static void draw_background(void)
{
    int i;
    u64 top = col64(C_SKY_TOP[0], C_SKY_TOP[1], C_SKY_TOP[2], 0x80);
    u64 hor = col64(C_HORIZON[0], C_HORIZON[1], C_HORIZON[2], 0x80);
    u64 bot = col64(C_VOID_BOT[0], C_VOID_BOT[1], C_VOID_BOT[2], 0x80);

    tri2(0, 0, top, SW, 0, top, 0, horizon_y, hor);
    tri2(SW, 0, top, SW, horizon_y, hor, 0, horizon_y, hor);
    tri2(0, horizon_y, hor, SW, horizon_y, hor, 0, SH, bot);
    tri2(SW, horizon_y, hor, SW, SH, bot, 0, SH, bot);

    for (i = 0; i < NSTARS; i++) {
        int b = star_b[i];
        rect(star_x[i], star_y[i], star_x[i] + 2.0f, star_y[i] + 2.0f, col64((float)b, (float)b, (float)(b + 20), 0x80));
    }
}

static void draw_piece(float xa, float xb, float z0, float z1, int n, int detail)
{
    const float *top = (n & 1) ? C_TOP_A : C_TOP_B;
    const float e = 0.16f;

    if (xb - xa < 0.05f) return;

    if (detail) {
        quad3(xa, 0, z0, xb, 0, z0, xb, -TILE_T, z0, xa, -TILE_T, z0, C_FRONT);
        if (cam_x < xa) quad3(xa, 0, z0, xa, 0, z1, xa, -TILE_T, z1, xa, -TILE_T, z0, C_WALL);
        if (cam_x > xb) quad3(xb, 0, z0, xb, 0, z1, xb, -TILE_T, z1, xb, -TILE_T, z0, C_WALL);
    }
    quad3(xa, 0, z0, xb, 0, z0, xb, 0, z1, xa, 0, z1, top);

    /* neon edges */
    quad3(xa, 0, z0, xa + e, 0, z0, xa + e, 0, z1, xa, 0, z1, C_NEON);
    quad3(xb - e, 0, z0, xb, 0, z0, xb, 0, z1, xb - e, 0, z1, C_NEON);
    if (!floor_in_row(n - 1, (xa + xb) * 0.5f))
        quad3(xa, 0, z0, xb, 0, z0, xb, 0, z0 + e, xa, 0, z0 + e, C_NEON);
}

static void draw_row(int n)
{
    Row *R;
    float z0 = n * ROWLEN, z1 = z0 + ROWLEN;
    int detail = (z0 - cam_z) < 75.0f;
    if (n < 0) return;
    R = ROW(n);
    if (R->id != n || !R->ok) return;

    if (R->hole) {
        draw_piece(R->l, R->hl, z0, z1, n, detail);
        draw_piece(R->hr, R->r, z0, z1, n, detail);
    } else {
        draw_piece(R->l, R->r, z0, z1, n, detail);
    }
}

static void draw_obstacle(float cx, float w, float h, float z0, float z1)
{
    float x0 = cx - w * 0.5f, x1 = cx + w * 0.5f;
    quad3(x0, 0, z0, x1, 0, z0, x1, h, z0, x0, h, z0, C_OB_FRONT);
    if (cam_x < x0) quad3(x0, 0, z0, x0, 0, z1, x0, h, z1, x0, h, z0, C_OB_SIDE);
    if (cam_x > x1) quad3(x1, 0, z0, x1, 0, z1, x1, h, z1, x1, h, z0, C_OB_SIDE);
    quad3(x0, h, z0, x1, h, z0, x1, h, z1, x0, h, z1, C_OB_TOP);
}

#define SEG 22

static void disc(float cx, float cy, float rx, float ry, float ax, float ay,
                 u64 cc, const u64 *ring)
{
    int i;
    float px[SEG + 1], py[SEG + 1];
    for (i = 0; i < SEG; i++) {
        float a = (float)i * (2.0f * 3.14159265f / SEG);
        px[i] = cx + cosf(a) * rx;
        py[i] = cy + sinf(a) * ry;
    }
    px[SEG] = px[0]; py[SEG] = py[0];
    for (i = 0; i < SEG; i++)
        tri2(ax, ay, cc, px[i], py[i], ring[i], px[i + 1], py[i + 1], ring[i + 1]);
}

static void disc_flat(float cx, float cy, float rx, float ry, u64 cc, u64 ce)
{
    u64 ring[SEG + 1];
    int i;
    for (i = 0; i <= SEG; i++) ring[i] = ce;
    disc(cx, cy, rx, ry, cx, cy, cc, ring);
}

static void draw_ball(void)
{
    float sx, sy, zc, r;
    int i;
    u64 ring[SEG + 1];

    if (!project(ball.x, ball.y, ball.z, &sx, &sy, &zc)) return;
    r = BALL_R * FOCAL / zc;

    /* ground shadow */
    if (!ball.fell) {
        float shx, shy, shz;
        if (project(ball.x, 0.0f, ball.z, &shx, &shy, &shz)) {
            float rs = BALL_R * FOCAL / shz;
            disc_flat(shx, shy - rs * 0.05f, rs * 1.15f, rs * 0.50f, col64(0, 0, 10, 0x50), col64(0, 0, 10, 0));
        }
    }

    /* neon glow */
    disc_flat(sx, sy, r * 1.55f, r * 1.55f, col64(70, 255, 225, 0x2A), col64(70, 255, 225, 0));

    /* body: off-centre apex gives a lit sphere */
    for (i = 0; i <= SEG; i++) {
        float a = (float)(i % SEG) * (2.0f * 3.14159265f / SEG);
        float lit = 0.5f + 0.5f * (cosf(a) * -0.55f + sinf(a) * -0.83f);
        ring[i] = col64(52.0f + 140.0f * lit, 60.0f + 142.0f * lit, 104.0f + 130.0f * lit, 0x80);
    }
    disc(sx, sy, r, r, sx - r * 0.28f, sy - r * 0.34f, col64(255, 255, 255, 0x80), ring);

    /* rolling spots */
    {
        static const float sk[4] = { 0.0f, 0.62f, -0.62f, 0.0f };
        static const float sphi[4] = { 0.0f, 1.7f, 3.3f, 4.7f };
        float roll = ball.z / BALL_R;
        int k;
        for (k = 0; k < 4; k++) {
            float th = roll + sphi[k];
            float q = sqrtf(1.0f - sk[k] * sk[k]);
            float ux = sk[k], uy = q * cosf(th), uz = q * sinf(th);
            float px = ball.x + BALL_R * ux, py = ball.y + BALL_R * uy, pz = ball.z + BALL_R * uz;
            float tx = cam_x - ball.x, ty = cam_y - ball.y, tz = cam_z - ball.z;
            float tl = sqrtf(tx * tx + ty * ty + tz * tz);
            float vis = (ux * tx + uy * ty + uz * tz) / tl;
            float spx, spy, spz;
            if (vis > 0.12f && project(px, py, pz, &spx, &spy, &spz)) {
                float rr = r * 0.20f * vis;
                disc_flat(spx, spy, rr, rr, col64(28, 34, 80, 0x70), col64(28, 34, 80, 0x70));
            }
        }
    }
}

static void render_world(void)
{
    int brow = (int)floorf(ball.z / ROWLEN);
    int n, k, ball_done = 0;

    draw_background();

    for (n = brow + VIEW_ROWS; n >= brow - 3; n--) draw_row(n);

    for (n = brow + VIEW_ROWS; n >= brow - 3; n--) {
        Row *R;
        if (n < 0) continue;
        R = ROW(n);
        if (R->id != n || !R->ok) continue;
        for (k = 0; k < R->nobs; k++) {
            float zc = (R->oz0[k] + R->oz1[k]) * 0.5f;
            if (!ball_done && zc < ball.z) { draw_ball(); ball_done = 1; }
            draw_obstacle(R->ox[k], R->ow[k], R->oh[k], R->oz0[k], R->oz1[k]);
        }
    }
    if (!ball_done) draw_ball();
}

static void draw_hud(void)
{
    char buf[32];
    const float mx = 44.0f, my = 34.0f;
    sprintf(buf, "SCORE %d", score);
    draw_text_sh(buf, mx, my, 3.0f, col64(235, 245, 255, 0x80));
    sprintf(buf, "BEST %d", best > score ? best : score);
    draw_text_sh(buf, SW - mx - text_w(buf, 3.0f), my, 3.0f, col64(70, 255, 225, 0x80));
}

static void draw_title(void)
{
    char buf[32];
    rect(0, 0, SW, SH, col64(0, 0, 14, 0x30));
    draw_text_c("SLOPE", SH * 0.16f, 14.0f, col64(70, 255, 225, 0x80));
    draw_text_c("PS2 EDITION", SH * 0.16f + 14.0f * 8.5f, 3.0f, col64(235, 245, 255, 0x80));
    if ((frame / 30) & 1) draw_text_c("PRESS START", SH * 0.66f, 4.0f, col64(255, 255, 255, 0x80));
    draw_text_c("D-PAD LEFT AND RIGHT TO STEER", SH * 0.80f, 2.0f, col64(200, 210, 240, 0x80));
    if (best > 0) {
        sprintf(buf, "BEST %d", best);
        draw_text_c(buf, SH * 0.88f, 3.0f, col64(70, 255, 225, 0x80));
    }
}

static void draw_dead(void)
{
    char buf[32];
    if (dead_t < 0.3f) return;
    rect(0, 0, SW, SH, col64(0, 0, 10, 0x40));
    draw_text_c("GAME OVER", SH * 0.20f, 9.0f, col64(255, 70, 80, 0x80));
    sprintf(buf, "SCORE %d", score);
    draw_text_c(buf, SH * 0.48f, 5.0f, col64(240, 248, 255, 0x80));
    sprintf(buf, "BEST %d", best);
    draw_text_c(buf, SH * 0.60f, 4.0f, col64(70, 255, 225, 0x80));
    if (dead_t > 0.8f && ((frame / 30) & 1))
        draw_text_c("PRESS START OR X", SH * 0.76f, 3.0f, col64(255, 255, 255, 0x80));
}

/* ------------------------------------------------------------------ */
/* init                                                                */
/* ------------------------------------------------------------------ */
static char padBuf[256] __attribute__((aligned(64)));

static void pad_init(void)
{
    int st, spin = 0;
    SifInitRpc(0);
    SifLoadModule("rom0:SIO2MAN", 0, NULL);
    SifLoadModule("rom0:PADMAN", 0, NULL);
    padInit(0);
    padPortOpen(0, 0, padBuf);
    do {
        st = padGetState(0, 0);
        spin++;
    } while (st != PAD_STATE_STABLE && st != PAD_STATE_FINDCTP1 && spin < 4000000);
}

static u32 pad_read(void)
{
    static u32 last = 0;
    struct padButtonStatus b;
    int st = padGetState(0, 0);
    if (st != PAD_STATE_STABLE && st != PAD_STATE_FINDCTP1) return last;
    if (padRead(0, 0, &b) == 0) return last;
    last = 0xFFFF ^ b.btns;
    return last;
}

static void gfx_init(void)
{
    gs = gsKit_init_global_custom(1024 * 1024, 64 * 1024);
    gs->PSM = GS_PSM_CT24;
    gs->PSMZ = GS_PSMZ_16S;
    gs->ZBuffering = GS_SETTING_OFF;
    gs->DoubleBuffering = GS_SETTING_ON;
    gs->PrimAlphaEnable = GS_SETTING_ON;

    dmaKit_init(D_CTRL_RELE_OFF, D_CTRL_MFD_OFF, D_CTRL_STS_UNSPEC, D_CTRL_STD_OFF, D_CTRL_RCYC_8, 1 << DMA_CHANNEL_GIF);
    dmaKit_chan_init(DMA_CHANNEL_GIF);

    gsKit_init_screen(gs);
    gsKit_mode_switch(gs, GS_ONESHOT);

    SW = (float)gs->Width;
    SH = (float)gs->Height;
    FOCAL = SW * 0.85f;
    DT = (gs->Mode == GS_MODE_PAL) ? (1.0f / 50.0f) : (1.0f / 60.0f);
}

static void stars_init(void)
{
    int i;
    cp = cosf(PITCH); sp = sinf(PITCH);
    horizon_y = clampf(SH * 0.5f - FOCAL * sp / cp, 20.0f, SH - 20.0f);
    for (i = 0; i < NSTARS; i++) {
        star_x[i] = rndf(0.0f, SW - 2.0f);
        star_y[i] = rndf(0.0f, horizon_y * 0.85f);
        star_b[i] = 90 + (int)(rnd() % 150);
    }
}

#ifdef SLOPE_TEST
int game_main(void)
#else
int main(void)
#endif
{
    u32 cur, prev = 0, pressed;

    pad_init();
    gfx_init();
    stars_init();
    start_title();

    for (;;) {
        cur = pad_read();
        pressed = cur & ~prev;
        prev = cur;

        switch (state) {
        case ST_TITLE:
            update_title(DT);
            if (pressed & (PAD_START | PAD_CROSS)) start_game();
            break;
        case ST_PLAY:
            update_play(DT, cur);
            break;
        default:
            update_dead(DT);
            if (dead_t > 0.8f && (pressed & (PAD_START | PAD_CROSS))) start_game();
            break;
        }

        FOCAL = SW * 0.85f * (1.0f - 0.10f * clampf((speed - 14.0f) / 46.0f, 0.0f, 1.0f));
        horizon_y = clampf(SH * 0.5f - FOCAL * sp / cp, 20.0f, SH - 20.0f);

        gsKit_clear(gs, col64(0, 0, 0, 0x80));
        render_world();
        if (state == ST_PLAY) draw_hud();
        else if (state == ST_TITLE) draw_title();
        else { draw_hud(); draw_dead(); }

        gsKit_queue_exec(gs);
        gsKit_sync_flip(gs);
        frame++;
    }
    return 0;
}
