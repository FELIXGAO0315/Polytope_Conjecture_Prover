/* PLUGIN file to use with plantri.c

   Compile:  cc -o plantri_mf -O4 '-DPLUGIN="count_multiset.c"' plantri.c

   Filters triangulations by vertex-degree multiset. One or more target
   multisets may be given by repeating the -D switch:

       plantri_mf -m5 -D5_24,6_4,18_1 -D5_25,6_2,19_1 29 -a

   outputs triangulations on 29 vertices whose degree multiset matches ANY
   of the listed targets exactly (every unlisted degree must have count 0).
   With a single -D the behaviour is identical to the original single-target
   version of this plugin.

   -Z ("once mode"): output at most ONE triangulation per target multiset
   per process. Intended for realizability DECISION across many targets in
   one sweep, where a popular multiset would otherwise flood stdout with
   millions of witnesses. -Z does not touch the generation tree: a target
   with zero output across cleanly-completed res/mod splits is still a
   proof by exhaustion that no such triangulation exists.

   IMPORTANT: this plugin does NOT modify the generation tree in any way (no
   pruning, no extension hooks). It is a pure leaf filter at output time, so
   exhaustiveness and isomorph-rejection are exactly those of unmodified
   plantri. All standard switches (-m5, -c, res/mod splitting, ...) remain
   available and behave as documented.
*/

#include <ctype.h>
#include <string.h>
#include <stdlib.h>

#define MF_MAXTARGETS 4096

static int target_cnt[MF_MAXTARGETS][MAXN+1];
static int target_seen[MF_MAXTARGETS];
static int n_targets = 0;
static int targets_sorted = 0;
static int once_mode = 0;

static int
mf_cmp(const void *a, const void *b)
{
    return memcmp(a, b, (MAXN+1)*sizeof(int));
}

static int
multiset_filter(int nbtot, int nbop, int doflip)
{
    int i, idx, cnt[MAXN+1];
    void *hit;

    if (n_targets == 0) return 1;
    /* Sort once, lazily, BEFORE any seen[] marking so indices stay stable. */
    if (!targets_sorted)
    {
        qsort(target_cnt, n_targets, sizeof(target_cnt[0]), mf_cmp);
        targets_sorted = 1;
    }
    for (i = 0; i <= MAXN; ++i) cnt[i] = 0;
    for (i = 0; i < nv; ++i) ++cnt[degree[i]];
    hit = bsearch(cnt, target_cnt, n_targets, sizeof(target_cnt[0]), mf_cmp);
    if (hit == NULL) return 0;
    if (once_mode)
    {
        idx = (int)(((char *)hit - (char *)target_cnt) / sizeof(target_cnt[0]));
        if (target_seen[idx]) return 0;
        target_seen[idx] = 1;
    }
    return 1;
}

#define FILTER multiset_filter

static void
parse_target(char *arg, int *pj)
{
    int j, k, v;

    if (n_targets >= MF_MAXTARGETS)
        { fprintf(stderr, ">E too many -D targets (max %d)\n", MF_MAXTARGETS); exit(1); }
    memset(target_cnt[n_targets], 0, sizeof(target_cnt[0]));
    j = *pj + 1;   /* arg[*pj] == 'D' */
    for (;;)
    {
        if (!isdigit((unsigned char)arg[j]))
            { fprintf(stderr, ">E -D expects k_v[,k_v...]\n"); exit(1); }
        k = atoi(arg+j);
        while (isdigit((unsigned char)arg[j])) ++j;
        if (arg[j] != '_')
            { fprintf(stderr, ">E -D expects k_v[,k_v...]\n"); exit(1); }
        ++j;
        if (!isdigit((unsigned char)arg[j]))
            { fprintf(stderr, ">E -D expects k_v[,k_v...]\n"); exit(1); }
        v = atoi(arg+j);
        while (isdigit((unsigned char)arg[j])) ++j;
        if (k < 0 || k > MAXN)
            { fprintf(stderr, ">E -D degree out of range\n"); exit(1); }
        target_cnt[n_targets][k] = v;
        if (arg[j] != ',') break;
        ++j;
    }
    ++n_targets;
    targets_sorted = 0;
    *pj = j - 1;   /* parser increments j past the last consumed char */
}

#define PLUGIN_SWITCHES \
    else if (arg[j] == 'D') parse_target(arg, &j); \
    else if (arg[j] == 'Z') once_mode = 1;
