#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <sstream>
#include <fstream>
#include <time.h>
#include <ctime>
#include <string>
#include <string.h>
#include <algorithm>
#include <climits>
#include<math.h>
#include <iomanip>

#include<vector>

// size limits (any instance within them is handled): up to 500 jobs, 100 machines, 20000 operations
#define MAXN 502
#define MAXM 102
#define MAXOPS 20002

using namespace std;
string inFile = "";//
int LB = 0;
unsigned seed = 666;

string outFile = "output.txt";//
int endTime = 20;//
int tabuDepth = 200;//
int searchDepth = 10e4;//
clock_t startTime;//
double bestTime;

//
int N, M; //NM
int queue[MAXOPS * 10], front, rear; //
int jm[MAXN][MAXM], jt[MAXN][MAXM];//
int job_time[MAXOPS];//
int jobS[MAXOPS], jobE[MAXOPS], jobM[MAXOPS], jobP[MAXOPS];//1234
int machine[MAXM][MAXN][3];//0MN12
int last_machine[MAXM];//
int ans_makespan;//
int this_makespan;//
int HASH_LEN = 1E8;//
// x is always the current hash (in [0,1e8)) plus 3 keys minus 3 keys (keys in [1,1e5]): one conditional add/subtract is the exact mod
static inline int ADAPT_hmod(long long x) { int r = (int)x; if (r < 0) r += 100000000; else if (r >= 100000000) r -= 100000000; return r; }
int number[MAXOPS][3];//12
// compact Zobrist tables: value of arc (a -> b) on a machine is stored at [a][job of b] (job 0 = dummy)
// the same three keys packed in one word (21-bit fields; keys <= 1e5 < 2^17): one load instead of three
// row stride N+1, allocated for the instance read
std::vector<unsigned long long> hpkv; unsigned long long* hpk_ = 0; int HW = 0;
#define HPK(a, j) hpk_[(a) * HW + (j)]
int jobOf[MAXOPS];
static const unsigned long long HPK_BIAS = (1ULL << 20) | (1ULL << 41) | (1ULL << 62);
// hashes of the solution obtained by the move (u, v, fwd) from the current one (exactly the original sums, then mod 1e8)
// visited-solution marks as bit arrays (same semantics as the original int arrays)
#define HBITS_WORDS ((100000000 + 63) / 64)
struct BitTab {
	unsigned long long w[HBITS_WORDS];
	inline bool get(int i) const { return (w[i >> 6] >> (i & 63)) & 1ULL; }
	inline void set(int i) { w[i >> 6] |= 1ULL << (i & 63); }
	inline void clear() { memset(w, 0, sizeof(w)); }
};
BitTab H1, H2, H3;
int hashObj1, hashObj2, hashObj3;
int r_change[MAXN], q_change[MAXN];
int blocks[MAXOPS * 2][3], q_save[MAXOPS];
int min_makespan;
int choose_machine[MAXOPS * 8], choose_u[MAXOPS * 8], choose_v[MAXOPS * 8], choose_forward[MAXOPS * 8];
int choose[MAXOPS * 8][4];
int min_machine, min_u, min_v, min_forward;
int iter, bestIter, lastClear = 0;
int noImprove;//
int kickPend = 0;
int tt = 10;//



void Read_Data();
void Init();
void Calculate_Q();
void Re_Coder();
void Jump_Pit(int jump_length, int per_flag);
bool If_Tabu(int u, int v, int fwd);
void Tabu_Search();
void show_solution();

// glibc rand() (TYPE_3 additive feedback generator) reimplemented inline: the SAME sequence for the same seed
// (verified against glibc on 2e6 draws for several seeds), without the lock glibc takes on every rand() call
struct GRand {
	unsigned s[31]; int f, b;
	void seed(unsigned sd) {
		int word = sd ? (int)sd : 1;
		s[0] = (unsigned)word;
		for (int k = 1; k < 31; k++) { long hi = word / 127773, lo = word % 127773; word = (int)(16807 * lo - 2836 * hi); if (word < 0) word += 2147483647; s[k] = (unsigned)word; }
		f = 3; b = 0;
		for (int k = 0; k < 310; k++) next();
	}
	inline int next() { s[f] += s[b]; int res = (int)(s[f] >> 1); if (++f >= 31) f = 0; if (++b >= 31) b = 0; return res; }
} grand_;
inline int Random(int n) {// 1-n 
	return grand_.next() % n + 1;
}
// flat precedence links (maintained at every move): machine pred/succ, job pred/succ, base in/out degrees
int MPa[MAXOPS], MSa[MAXOPS], JPa[MAXOPS], JSa[MAXOPS];
int indeg0[MAXOPS], outdeg0[MAXOPS];
inline void Link_Pos(int m, int p) {
	int x = machine[m][p][0];
	MPa[x] = (p > 1) ? machine[m][p - 1][0] : 0;
	MSa[x] = (p < N) ? machine[m][p + 1][0] : 0;
	indeg0[x] = (JPa[x] != 0) + (MPa[x] != 0);
	outdeg0[x] = (JSa[x] != 0) + (MSa[x] != 0);
}
void Build_Links() {
	for (int x = 1; x <= N * M; x++) {
		JPa[x] = (number[x][2] != 1) ? x - 1 : 0;
		JSa[x] = (number[x][2] != M) ? x + 1 : 0;
	}
	for (int m = 1; m <= M; m++) for (int p = 1; p <= N; p++) Link_Pos(m, p);
}
// full head recomputation (Kahn's algorithm on flat arrays)
int topo[MAXOPS], ntopo = 0, ordp[MAXOPS], tails_hi = -1; // topological order of the current graph (filled by Heads_Full)
void Heads_Full() {
	static int deg[MAXOPS];
	memcpy(deg, indeg0, sizeof(int) * (N * M + 1));
	int fr = 0, rr = 0;
	for (int m = 1; m <= M; m++) { int x = machine[m][1][0]; if (deg[x] == 0) topo[rr++] = x; }
	jobE[0] = 0;
	while (fr != rr) {
		int x = topo[fr++];
		int a = jobE[MPa[x]], b = jobE[JPa[x]];
		int st = a > b ? a : b;
		jobS[x] = st; jobE[x] = st + job_time[x];
		int y = JSa[x]; if (y && --deg[y] == 0) topo[rr++] = y;
		y = MSa[x]; if (y && --deg[y] == 0) topo[rr++] = y;
	}
	ntopo = rr;
	for (int i = 0; i < rr; i++) ordp[topo[i]] = i;
	tails_hi = rr - 1;
}
// incremental update after a move on one machine where u (was before v) and v now have arc v->u:
// the only arc violating the stored topological order is v->u. Pearce-Kelly local reorder of the
// window [ord u, ord v], then recompute heads on the suffix from ord u (exact, identical values).
void Heads_After_Move(int u, int v) {
	static int markF[MAXOPS], markB[MAXOPS], stk[MAXOPS], LB_[MAXOPS], LF_[MAXOPS], SL_[MAXOPS];
	static int st = 0;
	++st;
	int lb = ordp[u], ub = ordp[v];
	int sp = 0;
	markF[u] = st; stk[sp++] = u;
	while (sp) {
		int x = stk[--sp];
		int y = JSa[x]; if (y && markF[y] != st && ordp[y] < ub) { markF[y] = st; stk[sp++] = y; }
		y = MSa[x]; if (y && markF[y] != st && ordp[y] < ub) { markF[y] = st; stk[sp++] = y; }
	}
	markB[v] = st; stk[sp++] = v;
	while (sp) {
		int x = stk[--sp];
		int y = JPa[x]; if (y && markB[y] != st && ordp[y] > lb) { markB[y] = st; stk[sp++] = y; }
		y = MPa[x]; if (y && markB[y] != st && ordp[y] > lb) { markB[y] = st; stk[sp++] = y; }
	}
	int nb = 0, nf = 0, ns = 0;
	for (int i = lb; i <= ub; i++) {
		int x = topo[i];
		if (markB[x] == st) { LB_[nb++] = x; SL_[ns++] = i; }
		else if (markF[x] == st) { LF_[nf++] = x; SL_[ns++] = i; }
	}
	int k = 0;
	for (int i = 0; i < nb; i++, k++) { topo[SL_[k]] = LB_[i]; ordp[LB_[i]] = SL_[k]; }
	for (int i = 0; i < nf; i++, k++) { topo[SL_[k]] = LF_[i]; ordp[LF_[i]] = SL_[k]; }
	jobE[0] = 0;
	for (int i = lb; i < ntopo; i++) {
		int x = topo[i];
		int a = jobE[MPa[x]], b = jobE[JPa[x]];
		int s0 = a > b ? a : b;
		jobS[x] = s0; jobE[x] = s0 + job_time[x];
	}
	if (ub > tails_hi) tails_hi = ub;
}
// tail recomputation: reverse topological order, only the prefix that can have changed
void Tails_Full() {
	q_save[0] = 0;
	for (int i = tails_hi; i >= 0; i--) {
		int x = topo[i];
		int a = q_save[MSa[x]], b = q_save[JSa[x]];
		q_save[x] = (a > b ? a : b) + job_time[x];
	}
	tails_hi = -1;
}
inline int Mp(int i) { return MPa[i]; }  //
inline int Ms(int i) { return MSa[i]; }  //
inline int Jp(int i) { return JPa[i]; }  //
inline int Js(int i) { return JSa[i]; }  //

void Read_Data() {//
	int start_line[MAXN], temp_machine;
	memset(start_line, 0, sizeof(start_line));
	ifstream FIC;
	FIC.open(inFile);
	if (FIC.fail())
	{
		cout << "### Erreur open, File_Name ### " << inFile << endl;
		exit(0);
	}
	if (FIC.eof())
	{
		cout << "### Error open, File_Name ### " << inFile << endl;
		exit(0);
	}
	FIC >> N >> M;
	if (N < 1 || M < 1 || N > MAXN - 2 || M > MAXM - 2 || N * M > MAXOPS - 2) {
		cout << "### instance too large for the compiled limits: " << N << " x " << M << endl;
		exit(1);
	}
	for (int loop1 = 1; loop1 <= N; loop1++) {
		for (int loop2 = 1; loop2 <= M; loop2++) {
			FIC >> jm[loop1][loop2] >> jt[loop1][loop2]; // 
			++jm[loop1][loop2];//1
		}
	}
	FIC.close();
}

void Init() {//
	int job_line[MAXN], machine_line[MAXM], temp_machine, random_job;
	memset(job_line, 0, sizeof(job_line));
	memset(machine_line, 0, sizeof(machine_line));
	memset(machine, 0, sizeof(machine));
	memset(jobS, 0, sizeof(jobS)); memset(jobE, 0, sizeof(jobE)); memset(jobM, 0, sizeof(jobM)); memset(jobP, 0, sizeof(jobP));
	HW = N + 1;
	hpkv.assign((size_t)(N * M + 1) * HW, 0ULL); hpk_ = hpkv.data();
	H1.clear();
	H2.clear();
	H3.clear();

	for (int loop1 = 1; loop1 <= M * N; loop1++) {
		random_job = Random(N);
		while (job_line[random_job] >= M || random_job == 0) {
			random_job = (random_job + 1) % (N + 1);
		}
		temp_machine = jm[random_job][++job_line[random_job]];
		machine[temp_machine][++machine_line[temp_machine]][0] = (random_job - 1) * M + job_line[random_job];

		jobM[machine[temp_machine][machine_line[temp_machine]][0]] = temp_machine;
		jobP[machine[temp_machine][machine_line[temp_machine]][0]] = machine_line[temp_machine];
	}
	for (int loop1 = 1; loop1 <= N * M; loop1++) {  //numberjobjob 
		number[loop1][1] = ((loop1 - 1) / M) + 1;
		number[loop1][2] = ((loop1 - 1) % M) + 1;
	}
	Build_Links();
	job_time[0] = 0;
	for (int loop1 = 1; loop1 <= M * N; loop1++) {
		job_time[loop1] = jt[number[loop1][1]][number[loop1][2]];
	}

	//makespan
	int flag_ts[MAXOPS];
	int temp_operation, jp, mp, js, ms;
	rear = front = 0;
	memset(flag_ts, 0, sizeof(flag_ts));
	//mj,123queue
	for (int loop1 = 1; loop1 <= M; loop1++)
		flag_ts[machine[loop1][1][0]] = 1;
	for (int loop1 = 1; loop1 <= N; loop1++) {
		flag_ts[(loop1 - 1) * M + 1] += 2;
		if (flag_ts[(loop1 - 1) * M + 1] == 3)
			queue[rear++] = (loop1 - 1) * M + 1;
	}
	while (rear != front) {
		temp_operation = queue[front++];
		jp = Jp(temp_operation);
		mp = Mp(temp_operation);
		//if( jobE[0]!=0 )
		//	cout<<"wolegequ"<<endl;
		jobS[temp_operation] = machine[jobM[temp_operation]][jobP[temp_operation]][1] = max(jobE[mp], jobE[jp]);
		jobE[temp_operation] = machine[jobM[temp_operation]][jobP[temp_operation]][2] = jobS[temp_operation] + job_time[temp_operation];
		//flag[jobM[temp_operation]][jobP[temp_operation]]=-1;
		//start_line[jobM[temp_operation]]++;
		js = Js(temp_operation);
		ms = Ms(temp_operation);
		if (js != 0) {
			flag_ts[js] += 2;
			if (flag_ts[js] == 3)
				queue[rear++] = js;
		}
		if (ms != 0) {
			flag_ts[ms]++;
			if (flag_ts[ms] == 3)
				queue[rear++] = ms;
		}
	}

	int temp_max, loop;
	loop = 0;
	for (int loop1 = 1; loop1 <= M; loop1++) //makespan 
		if (loop1 == 1) {
			temp_max = 1;
			last_machine[++loop] = machine[loop1][N][0];
		}
		else if (machine[loop1][N][2] == machine[temp_max][N][2])
			last_machine[++loop] = machine[loop1][N][0];
		else if (machine[loop1][N][2] > machine[temp_max][N][2]) {
			temp_max = loop1;
			loop = 0;
			last_machine[++loop] = machine[loop1][N][0];
		}
	Heads_Full(); // same heads, also records the topological order
	last_machine[0] = loop;//mjlast_machine
	ans_makespan = this_makespan = machine[temp_max][N][2];// 

	//
	int temp_job1, temp_job2;
	H1.clear();
	H2.clear();
	H3.clear();
	hashObj1 = hashObj2 = hashObj3 = 0;
	for (int loop1 = 1; loop1 <= M; loop1++) {
		for (int loop2 = 1; loop2 < N; loop2++) {
			temp_job1 = machine[loop1][loop2][0];
			for (int loop3 = loop2 + 1; loop3 <= N; loop3++) {
				temp_job2 = machine[loop1][loop3][0];
				// the three keys of each arc, drawn in the original order, packed in 21-bit fields
				unsigned long long a1 = Random(1E5), b1 = Random(1E5), a2 = Random(1E5), b2 = Random(1E5), a3 = Random(1E5), b3 = Random(1E5);
				HPK(temp_job1, number[temp_job2][1]) = a1 | (a2 << 21) | (a3 << 42);
				HPK(temp_job2, number[temp_job1][1]) = b1 | (b2 << 21) | (b3 << 42);
				if (loop3 == loop2 + 1) {//
					hashObj1 = (hashObj1 + (int)a1) % HASH_LEN;
					hashObj2 = (hashObj2 + (int)a2) % HASH_LEN;
					hashObj3 = (hashObj3 + (int)a3) % HASH_LEN;
				}
			}
		}
	}

	for (int x = 0; x <= N * M; x++) jobOf[x] = number[x][1];
	H1.set(hashObj1);
	H2.set(hashObj2);
	H3.set(hashObj3);
}

void Critical_Path() {//
	// BFS over tight arcs from the last operations; critical ops recorded as per-machine position bitmasks,
	// blocks = maximal runs of set bits (same blocks, same order as the original scan)
	// per machine NWd words of position bits (positions 1..N), cleared for the M machines only
	static unsigned long long cbits[MAXM * ((MAXN + 64) / 64)];
	static int seen[MAXOPS];
	static int cstamp = 0;
	const int NWd = N / 64 + 1;
	++cstamp;
	memset(cbits, 0, sizeof(unsigned long long) * (M + 1) * NWd);
	front = rear = 0;
	for (int loop1 = 1; loop1 <= last_machine[0]; loop1++)
		queue[rear++] = last_machine[loop1];
	while (front != rear) {
		int operation = queue[front++];
		if (seen[operation] == cstamp) continue;
		seen[operation] = cstamp;
		int p = jobP[operation];
		cbits[jobM[operation] * NWd + (p >> 6)] |= 1ULL << (p & 63);
		int mp = MPa[operation], jp = JPa[operation], s0 = jobS[operation];
		if (mp != 0 && s0 == jobE[mp]) queue[rear++] = mp;
		if (jp != 0 && s0 == jobE[jp]) queue[rear++] = jp;
	}
	int loop3 = 0;
	for (int m = 1; m <= M; m++) {
		for (int w = 0; w < NWd; w++) {
			unsigned long long x = cbits[m * NWd + w];
			while (x) {
				int b = __builtin_ctzll(x);
				unsigned long long y = ~(x >> b);
				int len = y ? __builtin_ctzll(y) : 64 - b;
				int start = w * 64 + b, end = start + len - 1;
				x &= (len + b >= 64) ? 0ULL : (~0ULL << (b + len));
				if (b == 0 && w > 0 && loop3 > 0 && blocks[loop3][0] == m && blocks[loop3][2] == w * 64 - 1) {
					blocks[loop3][2] = end; // run continues across the word boundary
				}
				else {
					blocks[++loop3][0] = m;
					blocks[loop3][1] = start;
					blocks[loop3][2] = end;
				}
			}
		}
	}
	blocks[0][0] = loop3;// 
}

void Calculate_Q() {   //Q
	Tails_Full();
}

static inline void Move_Hash(int u, int v, int fwd, int& h1, int& h2, int& h3) {
	int m = jobM[u];
	int t1 = machine[m][jobP[u] - 1][0], t2 = machine[m][jobP[u] + 1][0];
	int t3 = machine[m][jobP[v] - 1][0], t4 = machine[m][jobP[v] + 1][0];
	int ju = jobOf[u], jv = jobOf[v], j4 = jobOf[t4];
	unsigned long long s;
	if (!fwd) s = HPK_BIAS + HPK(t1, jobOf[t2]) + HPK(v, ju) + HPK(u, j4) - HPK(t1, ju) - HPK(u, jobOf[t2]) - HPK(v, j4);
	else      s = HPK_BIAS + HPK(t1, jv) + HPK(v, ju) + HPK(t3, j4) - HPK(t1, ju) - HPK(t3, jv) - HPK(v, j4);
	const int MSK = (1 << 21) - 1, B = 1 << 20;
	h1 = ADAPT_hmod((long long)hashObj1 + (int)(s & MSK) - B);
	h2 = ADAPT_hmod((long long)hashObj2 + (int)((s >> 21) & MSK) - B);
	h3 = ADAPT_hmod((long long)hashObj3 + (int)((s >> 42) & MSK) - B);
}

void Recompute_Cmax() {
	int temp_max, loop2;
	loop2 = 0;
	for (int loop1 = 1; loop1 <= M; loop1++) { //makespan 
		if (loop1 == 1) {
			temp_max = 1;
			last_machine[++loop2] = machine[1][N][0];
		}
		else if (jobE[machine[loop1][N][0]] == jobE[machine[temp_max][N][0]]) {
			last_machine[++loop2] = machine[loop1][N][0];
		}
		else if (jobE[machine[loop1][N][0]] > jobE[machine[temp_max][N][0]]) {
			temp_max = loop1;
			loop2 = 0;
			last_machine[++loop2] = machine[loop1][N][0];
		}
	}
	last_machine[0] = loop2;//
	this_makespan = jobE[machine[temp_max][N][0]];//
}

void Re_Coder() {  //
	int front, rear, temp_save;
	int f_machine_number = jobP[min_u];
	int e_machine_number = jobP[min_v];
	int temp_machine, temp_job1, temp_job2, temp_job3, temp_job4;
	int temp_h1, temp_h2, temp_h3;
	int u, v;
	u = min_u;
	v = min_v;
	temp_machine = jobM[u];
	temp_job1 = machine[temp_machine][jobP[u] - 1][0];
	temp_job2 = machine[temp_machine][jobP[u] + 1][0];
	temp_job3 = machine[temp_machine][jobP[v] - 1][0];
	temp_job4 = machine[temp_machine][jobP[v] + 1][0];
	Move_Hash(u, v, min_forward, temp_h1, temp_h2, temp_h3); // before the sequence changes
	if (min_forward == 1) {        //  ,
		temp_save = machine[min_machine][e_machine_number][0];
		for (int loop1 = e_machine_number; loop1 >= f_machine_number; loop1--) {
			if (loop1 == f_machine_number) {
				machine[min_machine][loop1][0] = temp_save;
				jobP[temp_save] = f_machine_number;
			}
			else {
				machine[min_machine][loop1][0] = machine[min_machine][loop1 - 1][0];
				jobP[machine[min_machine][loop1][0]] = loop1;
			}
		}
	}
	else {
		temp_save = machine[min_machine][f_machine_number][0];
		for (int loop1 = f_machine_number; loop1 <= e_machine_number; loop1++) {
			if (loop1 == e_machine_number) {
				machine[min_machine][loop1][0] = temp_save;
				jobP[temp_save] = e_machine_number;
			}
			else {

				machine[min_machine][loop1][0] = machine[min_machine][loop1 + 1][0];
				jobP[machine[min_machine][loop1][0]] = loop1;
			}
		}
	}
	H1.set(temp_h1); H2.set(temp_h2); H3.set(temp_h3);//
	hashObj1 = temp_h1;
	hashObj2 = temp_h2;
	hashObj3 = temp_h3;
	for (int p = (f_machine_number > 1 ? f_machine_number - 1 : 1); p <= (e_machine_number < N ? e_machine_number + 1 : N); p++)
		Link_Pos(min_machine, p);
#ifdef CHECKINC
	Heads_After_Move(u, v);
	{ static int hs[MAXOPS], hq[MAXOPS]; int nm=N*M; for(int i=1;i<=nm;i++) hs[i]=jobS[i];
	  for (int i=0;i<ntopo;i++){int x=topo[i]; if(JPa[x]&&ordp[JPa[x]]>=i) {printf("BADORD\n");exit(1);} if(MPa[x]&&ordp[MPa[x]]>=i){printf("BADORD2\n");exit(1);} }
	  int th=tails_hi; Tails_Full(); for(int i=1;i<=nm;i++) hq[i]=q_save[i]; tails_hi=th;
	  Heads_Full(); for(int i=1;i<=nm;i++) if(hs[i]!=jobS[i]){printf("BADH\n");exit(1);}
	  Tails_Full(); for(int i=1;i<=nm;i++) if(hq[i]!=q_save[i]){printf("BADQ\n");exit(1);} tails_hi=-1; }
#else
	Heads_After_Move(u, v);
#endif

	Recompute_Cmax();
}

void Jump_Pit(int jump_length, int per_flag) {
	int u_machine_number, u_number, v_machine_number, v_number, job_number, temp_machine;
	int f_machine_number, e_machine_number, f_total_number, e_total_number;
	int jump_pit_cycle_number = jump_length;
	int loop;

	//

	if (!per_flag) {//
		while (jump_pit_cycle_number--) {
			Critical_Path();
			Calculate_Q();
			//memset(choose,0,sizeof(choose));
			loop = 0;
			for (int loop1 = 1; loop1 <= blocks[0][0]; loop1++) {
				e_machine_number = blocks[loop1][2];//
				f_machine_number = blocks[loop1][1]; //
				job_number = e_machine_number - f_machine_number + 1;//
				if (job_number == 1) continue;
				temp_machine = blocks[loop1][0];
				f_total_number = machine[temp_machine][f_machine_number][0];//
				e_total_number = machine[temp_machine][e_machine_number][0];//
				for (int loop2 = 2; loop2 <= job_number; loop2++) {//
					u_machine_number = f_machine_number;//u
					u_number = machine[temp_machine][u_machine_number][0];//u
					v_machine_number = f_machine_number + loop2 - 1;//v
					v_number = machine[temp_machine][v_machine_number][0];//v
					if (q_save[v_number] >= q_save[Js(u_number)]) {//uv
						choose[++loop][0] = temp_machine;
						choose[loop][1] = u_number;
						choose[loop][2] = v_number;
						choose[loop][3] = 0;
					}
					if (jobE[u_number] >= jobE[Jp(v_number)]) {//vU 
						choose[++loop][0] = temp_machine;
						choose[loop][1] = u_number;
						choose[loop][2] = v_number;
						choose[loop][3] = 1;
					}
				}
				for (int loop2 = 1; loop2 <= job_number - 1; loop2++) {//blocks
					u_machine_number = f_machine_number + loop2 - 1;//u
					u_number = machine[temp_machine][u_machine_number][0];//u
					v_machine_number = e_machine_number;
					v_number = machine[temp_machine][e_machine_number][0];//e_total_number
					if (q_save[v_number] >= q_save[Js(u_number)]) {//uV
						choose[++loop][0] = temp_machine;
						choose[loop][1] = u_number;
						choose[loop][2] = v_number;
						choose[loop][3] = 0;
					}
					if (jobE[u_number] >= jobE[Jp(v_number)]) {//vU
						choose[++loop][0] = temp_machine;
						choose[loop][1] = u_number;
						choose[loop][2] = v_number;
						choose[loop][3] = 1;
					}
				}
			}
			choose[0][0] = loop;//
			if (loop == 0)cout << "" << endl;
			int random_choose = Random(loop);// 1----loop
			min_machine = choose[random_choose][0];
			min_u = choose[random_choose][1];
			min_v = choose[random_choose][2];
			min_forward = choose[random_choose][3];
			Re_Coder();
		}
	}
	else {//
		while (jump_pit_cycle_number--) {
			Critical_Path();
			Calculate_Q();
			loop = 0;
			for (int loop1 = 1; loop1 <= M; loop1++) {
				temp_machine = loop1;
				for (int loop2 = 1; loop2 < N; loop2++) {// 
					u_machine_number = loop2;//u 
					u_number = machine[temp_machine][u_machine_number][0];//u
					for (int loop3 = loop2 + 1; loop3 <= N; loop3++) {//				
						v_machine_number = loop3;//v 
						v_number = machine[temp_machine][v_machine_number][0];//v 
						if (q_save[v_number] >= q_save[Js(u_number)]) {//uv 
							choose[++loop][0] = temp_machine;
							choose[loop][1] = u_number;
							choose[loop][2] = v_number;
							choose[loop][3] = 0;
						}
						if (jobE[u_number] >= jobE[Jp(v_number)]) {//vU  
							choose[++loop][0] = temp_machine;
							choose[loop][1] = u_number;
							choose[loop][2] = v_number;
							choose[loop][3] = 1;
						}
					}
				}
			}
			choose[0][0] = loop;//
			if (loop == 0)cout << "" << endl;
			int random_choose = Random(loop);// 1----loop

			min_machine = choose[random_choose][0];
			min_u = choose[random_choose][1];
			min_v = choose[random_choose][2];
			min_forward = choose[random_choose][3];
			Re_Coder();
		}

	}

}


bool If_Tabu(int u, int v, int fwd) {//10fwd0uvfwd1vu
	// branch-free: tabu iff the 3 bits are set; marking the 3 bits is a no-op when they all are, so it is done
	// unconditionally (same verdicts and same marks as the original get/set; the dummy draw is kept for the stream)
	int h1, h2, h3;
	Move_Hash(u, v, fwd, h1, h2, h3);
	unsigned long long* p1 = &H1.w[h1 >> 6]; unsigned long long* p2 = &H2.w[h2 >> 6]; unsigned long long* p3 = &H3.w[h3 >> 6];
	unsigned long long m1 = 1ULL << (h1 & 63), m2 = 1ULL << (h2 & 63), m3 = 1ULL << (h3 & 63);
	unsigned long long w1 = *p1, w2 = *p2, w3 = *p3;
	bool tabu = ((w1 & m1) != 0) & ((w2 & m2) != 0) & ((w3 & m3) != 0);
	*p1 = w1 | m1; *p2 = w2 | m2; *p3 = w3 | m3;
	if (!tabu) grand_.next(); // the original drew Random(100) here (always <= 100)
	return tabu;
}

void Tabu_Search() {//
	int temp_makespan, temp_machine, u_machine_number, u_number, v_machine_number, v_number, w_number, job_number;
	int choose_number, f_machine_number, e_machine_number;
	int end_number;//
	int start_number;//

	min_makespan = INT_MAX, choose_number = 0; // (was HASH_LEN = 1e8: no move could be chosen once the makespan exceeds 1e8)
	Critical_Path();//

	Calculate_Q();//Q;

	//N6
	for (int loop1 = 1; loop1 <= blocks[0][0]; loop1++) {
		e_machine_number = blocks[loop1][2];//
		f_machine_number = blocks[loop1][1]; // 
		job_number = e_machine_number - f_machine_number + 1;// 
		if (job_number == 1) continue;
		temp_machine = blocks[loop1][0];
		for (int loop2 = 2; loop2 <= job_number; loop2++) {//V 
			u_machine_number = f_machine_number;//u 
			u_number = machine[temp_machine][u_machine_number][0];//u
			v_machine_number = f_machine_number + loop2 - 1;//v 
			v_number = machine[temp_machine][v_machine_number][0];//v 
			if (q_save[v_number] >= q_save[Js(u_number)] && Jp(u_number) != 0 && !If_Tabu(u_number, v_number, 0)) {//uv 
				int tmx_ = 0; bool cut_ = false; // exact early abort: the candidate is kept only if its estimate <= min_makespan
				for (int loop3 = loop2 + 1; loop3 >= 2; loop3--) {//(w,n)
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w
					if (loop3 == loop2 + 1 && Ms(v_number) == 0)//v   U 1
						q_change[loop3] = job_time[u_number] + q_save[Js(u_number)];
					else if (loop3 == loop2 + 1)//U 2
						q_change[loop3] = job_time[u_number] + max(q_save[Js(u_number)], q_save[Ms(v_number)]);
					else if (loop3 == loop2)//v
						q_change[loop3] = job_time[v_number] + max(q_save[Js(v_number)], q_change[loop3 + 1]);
					else //w
						q_change[loop3] = job_time[w_number] + max(q_save[Js(w_number)], q_change[loop3 + 1]);
				}
				for (int loop3 = 2; loop3 <= loop2 + 1; loop3++) {//(0,w)
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w 
					if (loop3 == 2 && Mp(u_number) == 0)//u  L1  1
						r_change[loop3] = jobE[Jp(w_number)];
					else if (loop3 == 2)//L1  2
						r_change[loop3] = max(jobE[Jp(w_number)], jobE[Mp(u_number)]);
					else if (loop3 == loop2 + 1)//u
						r_change[loop3] = max(jobE[Jp(u_number)], r_change[loop3 - 1] + job_time[v_number]);//(0,u)
					else //w
						r_change[loop3] = max(jobE[Jp(w_number)], r_change[loop3 - 1] + job_time[Mp(w_number)]);
					{ int t_ = r_change[loop3] + q_change[loop3]; if (t_ > min_makespan) { cut_ = true; break; } if (t_ > tmx_) tmx_ = t_; }
				}
				temp_makespan = cut_ ? INT_MAX : tmx_;

				if (temp_makespan <= min_makespan) {
					if (temp_makespan < min_makespan) {
						min_makespan = temp_makespan;
						choose_number = 1;
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 0;
						//choose_forward[0]=0;
					}
					else if (temp_makespan == min_makespan) {
						if (choose_number < MAXOPS * 8 - 1) choose_number++; // capacity guard (never reached in practice)
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 0;
						//choose_forward[0]=0;
					}
				}

			}

			// de-duplication: the adjacent swap (loop2 == 2) was already tested as "u after v" above (identical hash, so this copy is always tabu)
			if (jobE[u_number] >= jobE[Jp(v_number)] && Jp(u_number) != 0 && loop2 != 2 && !If_Tabu(u_number, v_number, 1)) {//vU 
				int tmx_ = 0; bool cut_ = false; // exact early abort: the candidate is kept only if its estimate <= min_makespan
				for (int loop3 = loop2 - 1; loop3 >= 0; loop3--) {//(w,n)
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];
					if (loop3 == loop2 - 1 && Ms(v_number) == 0)//Lk 1
						q_change[loop3] = job_time[w_number] + q_save[Js(w_number)];
					else if (loop3 == loop2 - 1)//Lk 2
						q_change[loop3] = job_time[w_number] + max(q_save[Js(w_number)], q_save[Ms(v_number)]);
					else if (loop3 == 0)//v
						q_change[loop3] = job_time[v_number] + max(q_save[Js(v_number)], q_change[loop3 + 1]);
					else //w
						q_change[loop3] = job_time[w_number] + max(q_save[Js(w_number)], q_change[loop3 + 1]);
				}
				for (int loop3 = 0; loop3 <= loop2 - 1; loop3++) {//(0,w)
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];
					if (loop3 == 0 && Mp(u_number) == 0)//v 1     f_machine_number-1==0
						r_change[loop3] = jobE[Jp(v_number)];
					else if (loop3 == 0)//v 2
						r_change[loop3] = max(jobE[Jp(v_number)], jobE[Mp(u_number)]);
					else if (loop3 == 1)//u
						r_change[loop3] = max(jobE[Jp(u_number)], r_change[loop3 - 1] + job_time[v_number]);
					else //w
						r_change[loop3] = max(jobE[Jp(w_number)], r_change[loop3 - 1] + job_time[Mp(w_number)]);
					{ int t_ = r_change[loop3] + q_change[loop3]; if (t_ > min_makespan) { cut_ = true; break; } if (t_ > tmx_) tmx_ = t_; }
				}

				temp_makespan = cut_ ? INT_MAX : tmx_;

				if (temp_makespan <= min_makespan) {
					if (temp_makespan < min_makespan) {
						min_makespan = temp_makespan;
						choose_number = 1;
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 1;
						//choose_forward[0]=0;
					}
					else if (temp_makespan == min_makespan) {
						if (choose_number < MAXOPS * 8 - 1) choose_number++; // capacity guard (never reached in practice)
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 1;
						//choose_forward[0]=0;
					}
				}
			}
		}

		for (int loop2 = 1; loop2 <= job_number - 1; loop2++) {//blocks 
			u_machine_number = f_machine_number + loop2 - 1;//u 
			u_number = machine[temp_machine][u_machine_number][0];//u
			v_machine_number = e_machine_number;
			v_number = machine[temp_machine][e_machine_number][0];//e_total_number
			if (q_save[v_number] >= q_save[Js(u_number)] && Js(v_number) != 0 && !(loop2 == 1 && Jp(u_number) != 0) && !If_Tabu(u_number, v_number, 0)) {//uv 
				int tmx_ = 0; bool cut_ = false; // exact early abort: the candidate is kept only if its estimate <= min_makespan
				for (int loop3 = job_number + 1; loop3 >= loop2 + 1; loop3--) {// (w,n)
					int w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w 
					if (loop3 == job_number + 1 && Ms(v_number) == 0)//u  1
						q_change[loop3] = job_time[u_number] + q_save[Js(u_number)];
					else if (loop3 == job_number + 1)//u  2
						q_change[loop3] = job_time[u_number] + max(q_save[Js(u_number)], q_save[Ms(v_number)]);
					else if (loop3 == job_number)//v
						q_change[loop3] = job_time[v_number] + max(q_save[Js(v_number)], q_change[loop3 + 1]);
					else //w
						q_change[loop3] = job_time[w_number] + max(q_save[Js(w_number)], q_change[loop3 + 1]);
				}
				for (int loop3 = loop2 + 1; loop3 <= job_number + 1; loop3++) {//(0,w)    e_blocks_number=job_number
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w 
					if (loop3 == loop2 + 1 && Mp(u_number) == 0)//L1  1
						r_change[loop3] = jobE[Jp(w_number)];
					else if (loop3 == loop2 + 1)//L1  2
						r_change[loop3] = max(jobE[Jp(w_number)], jobE[Mp(u_number)]);
					else if (loop3 == job_number + 1)//u
						r_change[loop3] = max(jobE[Jp(u_number)], r_change[loop3 - 1] + job_time[v_number]);
					else //w
						r_change[loop3] = max(jobE[Jp(w_number)], r_change[loop3 - 1] + job_time[Mp(w_number)]);
					{ int t_ = r_change[loop3] + q_change[loop3]; if (t_ > min_makespan) { cut_ = true; break; } if (t_ > tmx_) tmx_ = t_; }
				}
				temp_makespan = cut_ ? INT_MAX : tmx_;

				if (temp_makespan <= min_makespan) {
					if (temp_makespan < min_makespan) {
						min_makespan = temp_makespan;
						choose_number = 1;
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 0;
						//	choose_forward[0]=0;
					}
					else if (temp_makespan == min_makespan) {
						if (choose_number < MAXOPS * 8 - 1) choose_number++; // capacity guard (never reached in practice)
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 0;
						//	choose_forward[0]=0;
					}
				}
			
			}
			if (jobE[u_number] >= jobE[Jp(v_number)] && Js(v_number) != 0 && loop2 != job_number - 1 && !(loop2 == 1 && Jp(u_number) != 0) && !If_Tabu(u_number, v_number, 1)) {//vU 
				int tmx_ = 0; bool cut_ = false; // exact early abort: the candidate is kept only if its estimate <= min_makespan
				for (int loop3 = job_number - 1; loop3 >= loop2 - 1; loop3--) {//(w,n)
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w
					if (loop3 == (job_number - 1) && Ms(v_number) == 0)//lk 1
						q_change[loop3] = job_time[w_number] + q_save[Js(w_number)];
					else if (loop3 == job_number - 1)//lk 2
						q_change[loop3] = job_time[w_number] + max(q_save[Js(w_number)], q_save[Ms(v_number)]);
					else if (loop3 == loop2 - 1)//v
						q_change[loop3] = job_time[v_number] + max(q_save[Js(v_number)], q_change[loop3 + 1]);
					else //w
						q_change[loop3] = job_time[w_number] + max(q_save[Js(w_number)], q_change[loop3 + 1]);
				}
				for (int loop3 = loop2 - 1; loop3 <= job_number - 1; loop3++) {//(0,w)   
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w    
					if (loop3 == (loop2 - 1) && Mp(u_number) == 0)   //v  1
						r_change[loop3] = jobE[Jp(v_number)];
					else if (loop3 == loop2 - 1)//v 2
						r_change[loop3] = max(jobE[Jp(v_number)], jobE[Mp(u_number)]);
					else if (loop3 == loop2)//u
						r_change[loop3] = max(jobE[Jp(u_number)], r_change[loop3 - 1] + job_time[v_number]);
					else //w
						r_change[loop3] = max(jobE[Jp(w_number)], r_change[loop3 - 1] + job_time[Mp(w_number)]);
					{ int t_ = r_change[loop3] + q_change[loop3]; if (t_ > min_makespan) { cut_ = true; break; } if (t_ > tmx_) tmx_ = t_; }
				}
				temp_makespan = cut_ ? INT_MAX : tmx_;

				////
				if (temp_makespan <= min_makespan) {
					if (temp_makespan < min_makespan) {
						min_makespan = temp_makespan;
						choose_number = 1;
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 1;
						//	choose_forward[0]=0;
					}
					else if (temp_makespan == min_makespan) {
						if (choose_number < MAXOPS * 8 - 1) choose_number++; // capacity guard (never reached in practice)
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 1;
						//choose_forward[0]=0;
					}
				}
			
			}
		}
	}

	//u
#if 1 
	for (int loop1 = 1; loop1 <= blocks[0][0]; loop1++) {
		e_machine_number = N;//
		f_machine_number = blocks[loop1][1]; // 
		job_number = e_machine_number - f_machine_number + 1;// 
		if (job_number == 1) continue;
		temp_machine = blocks[loop1][0];
		for (int loop2 = blocks[loop1][2]+1; loop2 <= job_number; loop2++) {//V 
			u_machine_number = f_machine_number;//u 
			u_number = machine[temp_machine][u_machine_number][0];//u
			v_machine_number = f_machine_number + loop2 - 1;//v 
			v_number = machine[temp_machine][v_machine_number][0];//v 
			if (q_save[v_number] < q_save[Js(u_number)]) break; // offer S1_v3: tails nonincreasing along a machine: no later v is feasible
			if (q_save[v_number] >= q_save[Js(u_number)] && Jp(u_number) != 0 && !If_Tabu(u_number, v_number, 0)) {//uv 
				int tmx_ = 0; bool cut_ = false; // exact early abort: the candidate is kept only if its estimate <= min_makespan
				for (int loop3 = loop2 + 1; loop3 >= 2; loop3--) {//(w,n)
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w
					if (loop3 == loop2 + 1 && Ms(v_number) == 0)//v   U 1
						q_change[loop3] = job_time[u_number] + q_save[Js(u_number)];
					else if (loop3 == loop2 + 1)//U 2
						q_change[loop3] = job_time[u_number] + max(q_save[Js(u_number)], q_save[Ms(v_number)]);
					else if (loop3 == loop2)//v
						q_change[loop3] = job_time[v_number] + max(q_save[Js(v_number)], q_change[loop3 + 1]);
					else //w
						q_change[loop3] = job_time[w_number] + max(q_save[Js(w_number)], q_change[loop3 + 1]);
				}
				for (int loop3 = 2; loop3 <= loop2 + 1; loop3++) {//(0,w)
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w 
					if (loop3 == 2 && Mp(u_number) == 0)//u  L1  1
						r_change[loop3] = jobE[Jp(w_number)];
					else if (loop3 == 2)//L1  2
						r_change[loop3] = max(jobE[Jp(w_number)], jobE[Mp(u_number)]);
					else if (loop3 == loop2 + 1)//u
						r_change[loop3] = max(jobE[Jp(u_number)], r_change[loop3 - 1] + job_time[v_number]);//(0,u)
					else //w
						r_change[loop3] = max(jobE[Jp(w_number)], r_change[loop3 - 1] + job_time[Mp(w_number)]);
					{ int t_ = r_change[loop3] + q_change[loop3]; if (t_ > min_makespan) { cut_ = true; break; } if (t_ > tmx_) tmx_ = t_; }
				}
				temp_makespan = cut_ ? INT_MAX : tmx_;

				if (temp_makespan <= min_makespan) {
					if (temp_makespan < min_makespan) {
						min_makespan = temp_makespan;
						choose_number = 1;
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 0;
						//choose_forward[0]=0;
						//cout << "N3" << endl;

					}
					else if (temp_makespan == min_makespan) {
						if (choose_number < MAXOPS * 8 - 1) choose_number++; // capacity guard (never reached in practice)
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 0;
						//choose_forward[0]=0;
					}
				}

			}
		}
	}
#endif

	//v
#if 1 
	for (int loop1 = 1; loop1 <= blocks[0][0]; loop1++) {
		e_machine_number = blocks[loop1][2];//
		f_machine_number = 1; // 
		job_number = e_machine_number - f_machine_number + 1;// 
		if (job_number == 1) continue;
		temp_machine = blocks[loop1][0];
		// offer S1_v3: heads are nondecreasing along a machine: the feasible u (jobE[u] >= jobE[Jp(v)]) form a suffix of
		// positions [p0, blockstart-1]; start the scan at p0 (same candidates, same order)
		int p0 = 1;
		{
			int vv = machine[temp_machine][e_machine_number][0];
			if (Js(vv) == 0) continue;
			int X = jobE[Jp(vv)];
			int hi = blocks[loop1][1] - 1; if (hi > job_number - 1) hi = job_number - 1;
			int lo = 1, h2 = hi + 1;
			while (lo < h2) { int mid = (lo + h2) >> 1; if (jobE[machine[temp_machine][mid][0]] >= X) h2 = mid; else lo = mid + 1; }
			p0 = lo;
		}
		for (int loop2 = p0; loop2 <= job_number - 1; loop2++) {//blocks 
			u_machine_number = f_machine_number + loop2 - 1;//u 
			if (u_machine_number >= blocks[loop1][1])break;
			u_number = machine[temp_machine][u_machine_number][0];//u
			v_machine_number = e_machine_number;
			v_number = machine[temp_machine][e_machine_number][0];//e_total_number
			if (jobE[u_number] >= jobE[Jp(v_number)] && Js(v_number) != 0 && !If_Tabu(u_number, v_number, 1)) {//vU 
				int tmx_ = 0; bool cut_ = false; // exact early abort: the candidate is kept only if its estimate <= min_makespan
				for (int loop3 = job_number - 1; loop3 >= loop2 - 1; loop3--) {//(w,n)
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w
					if (loop3 == (job_number - 1) && Ms(v_number) == 0)//lk 1
						q_change[loop3] = job_time[w_number] + q_save[Js(w_number)];
					else if (loop3 == job_number - 1)//lk 2
						q_change[loop3] = job_time[w_number] + max(q_save[Js(w_number)], q_save[Ms(v_number)]);
					else if (loop3 == loop2 - 1)//v
						q_change[loop3] = job_time[v_number] + max(q_save[Js(v_number)], q_change[loop3 + 1]);
					else //w
						q_change[loop3] = job_time[w_number] + max(q_save[Js(w_number)], q_change[loop3 + 1]);
				}
				for (int loop3 = loop2 - 1; loop3 <= job_number - 1; loop3++) {//(0,w)   
					w_number = machine[temp_machine][f_machine_number + loop3 - 1][0];//w    
					if (loop3 == (loop2 - 1) && Mp(u_number) == 0)   //v  1
						r_change[loop3] = jobE[Jp(v_number)];
					else if (loop3 == loop2 - 1)//v 2
						r_change[loop3] = max(jobE[Jp(v_number)], jobE[Mp(u_number)]);
					else if (loop3 == loop2)//u
						r_change[loop3] = max(jobE[Jp(u_number)], r_change[loop3 - 1] + job_time[v_number]);
					else //w
						r_change[loop3] = max(jobE[Jp(w_number)], r_change[loop3 - 1] + job_time[Mp(w_number)]);
					{ int t_ = r_change[loop3] + q_change[loop3]; if (t_ > min_makespan) { cut_ = true; break; } if (t_ > tmx_) tmx_ = t_; }
				}
				temp_makespan = cut_ ? INT_MAX : tmx_;

				////
				if (temp_makespan <= min_makespan) {
					if (temp_makespan < min_makespan) {
						min_makespan = temp_makespan;
						choose_number = 1;
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 1;
						//	choose_forward[0]=0;
						//cout << "N4" << endl;
					}
					else if (temp_makespan == min_makespan) {
						if (choose_number < MAXOPS * 8 - 1) choose_number++; // capacity guard (never reached in practice)
						choose_machine[choose_number] = temp_machine;
						choose_u[choose_number] = u_number;
						choose_v[choose_number] = v_number;
						choose_forward[choose_number] = 1;
						//choose_forward[0]=0;
					}
				}


			}
		}




	}
#endif

	if (choose_number == 0) {
		Jump_Pit(2, 0);
	}
	else {
		choose_number = Random(choose_number);
		min_machine = choose_machine[choose_number];
		min_u = choose_u[choose_number];
		min_v = choose_v[choose_number];
		min_forward = choose_forward[choose_number];
		Re_Coder();
	}


}

void show_solution() {//

	ofstream fout(outFile);
	//fout << inFile << endl << endl;
	fout << "************gantt chart:************" << endl;
	for (int loop1 = 1; loop1 <= M; loop1++) {
		for (int loop2 = 1; loop2 <= N; loop2++) {
			fout << setw(2) << number[machine[loop1][loop2][0]][1] << "," << setw(2) << number[machine[loop1][loop2][0]][2]
				<< ": [" << left << setw(5) << machine[loop1][loop2][1] << " "
				<< right << setw(5) << machine[loop1][loop2][2] << "]	";
		}
		fout << endl;
	}
	fout << endl;


	for (int loop1 = 1; loop1 <= M; loop1++) {
		for (int loop2 = 1; loop2 <= N; loop2++) {
			cout << setw(5) << machine[loop1][loop2][0] << "	";
		}
		cout << endl;
	}
	cout << "hashObj1=" << hashObj1 << endl;
}


// ---- adapter (I/O only): best schedule, trivial lower bound, solution file ----------------------------------------
int ADAPT_best[MAXM][MAXN];
void ADAPT_snapshot() {
	for (int k = 1; k <= M; k++)
		for (int p = 1; p <= N; p++)
			ADAPT_best[k][p] = machine[k][p][0];
}
// offer S1_v5: restore the best schedule as the current solution (orders, links, heads, makespan, hash value)
void Restore_From(int (*arr)[MAXN]) {
	for (int k = 1; k <= M; k++)
		for (int p = 1; p <= N; p++) { int x = arr[k][p]; machine[k][p][0] = x; jobP[x] = p; }
	Build_Links();
	Heads_Full();
	Recompute_Cmax();
	long long h1 = 0, h2 = 0, h3 = 0;
	const unsigned long long MSK = (1ULL << 21) - 1;
	for (int k = 1; k <= M; k++)
		for (int p = 1; p < N; p++) {
			unsigned long long key = HPK(machine[k][p][0], jobOf[machine[k][p + 1][0]]);
			h1 += key & MSK; h2 += (key >> 21) & MSK; h3 += (key >> 42) & MSK;
		}
	hashObj1 = (int)(h1 % HASH_LEN); hashObj2 = (int)(h2 % HASH_LEN); hashObj3 = (int)(h3 % HASH_LEN);
}
#ifndef ENDGAME_FRAC
#define ENDGAME_FRAC 0.10
#endif
int endgame = 0;
// elite end game: a pool of the best distinct memory-episode bests (recorded only; the walk is not changed before the
// end game); the end game is split into EG_K phases, phase i polishes pool member i (best first): restore it, empty
// memory, every kick restarts from the best solution found in this phase (its anchor)
#ifndef EG_K
#define EG_K 8
#endif
int poolSeq[EG_K][MAXM][MAXN], poolCost[EG_K], poolH[EG_K][3], poolN = 0;
int epSeq[MAXM][MAXN], epCost = INT_MAX, epH[3], epValid = 0;
int anchorSeq[MAXM][MAXN], anchorCost = INT_MAX, anchorCrit = INT_MAX;
long long egTieUp = 0; int anchorH[3];
// number of critical operations of the current solution (union of critical paths); secondary criterion for anchors
int Crit_Count() {
	Critical_Path();
	int c = 0;
	for (int b = 1; b <= blocks[0][0]; b++) c += blocks[b][2] - blocks[b][1] + 1;
	return c;
}
int egPhase = -1; double egStart = 0, egLen = 0;
static inline void Copy_Current(int (*dst)[MAXN]) {
	for (int k = 1; k <= M; k++) for (int p = 1; p <= N; p++) dst[k][p] = machine[k][p][0];
}
int Pool_Worst() {
	if (poolN < EG_K) return INT_MAX;
	int w = 0; for (int i = 1; i < poolN; i++) if (poolCost[i] > poolCost[w]) w = i;
	return poolCost[w];
}
void Episode_Track() { // after each walk iteration, before the end game
	if (this_makespan < epCost) {
		epCost = this_makespan;
		if (epCost < Pool_Worst()) { Copy_Current(epSeq); epH[0] = hashObj1; epH[1] = hashObj2; epH[2] = hashObj3; epValid = 1; }
		else epValid = 0;
	}
}
void Episode_End() { // at each memory wipe: the episode best enters the pool if it is distinct and good enough
	if (epValid) {
		int dup = -1;
		for (int i = 0; i < poolN; i++) if (poolH[i][0] == epH[0] && poolH[i][1] == epH[1] && poolH[i][2] == epH[2]) dup = i;
		if (dup < 0) {
			int slot = -1;
			if (poolN < EG_K) slot = poolN++;
			else { int w = 0; for (int i = 1; i < poolN; i++) if (poolCost[i] > poolCost[w]) w = i; if (epCost < poolCost[w]) slot = w; }
			if (slot >= 0) {
				memcpy(poolSeq[slot], epSeq, sizeof(epSeq)); poolCost[slot] = epCost;
				poolH[slot][0] = epH[0]; poolH[slot][1] = epH[1]; poolH[slot][2] = epH[2];
			}
		}
	}
	epCost = INT_MAX; epValid = 0;
}
void EG_Begin_Phase(int i) {
	egPhase = i;
	Restore_From(poolSeq[i]);
	Copy_Current(anchorSeq); anchorCost = this_makespan; anchorCrit = Crit_Count(); anchorH[0] = hashObj1; anchorH[1] = hashObj2; anchorH[2] = hashObj3;
	H1.clear(); H2.clear(); H3.clear();
	H1.set(hashObj1); H2.set(hashObj2); H3.set(hashObj3);
	noImprove = 0; lastClear = iter;
}
void Restore_Best() { Restore_From(ADAPT_best); }
int ADAPT_trivial_lb() {
	int lb = 0;
	static int load[MAXM];
	memset(load, 0, sizeof(load));
	for (int j = 1; j <= N; j++) {
		int tot = 0;
		for (int k = 1; k <= M; k++) { tot += jt[j][k]; load[jm[j][k]] += jt[j][k]; }
		if (tot > lb) lb = tot;
	}
	for (int k = 1; k <= M; k++) if (load[k] > lb) lb = load[k];
	return lb;
}
void ADAPT_write(const string& path) {
	ofstream f(path.c_str());
	f << N << " " << M << " " << ans_makespan << "\n";
	for (int k = 1; k <= M; k++) {
		for (int p = 1; p <= N; p++) f << number[ADAPT_best[k][p]][1] << (p < N ? " " : "\n");
	}
	f.close();
}

int main(int argc, char** argv)
{
	string ADAPT_sol = "";
	double ADAPT_T = 20.0;
	if (argc < 3) { cout << "usage: solver <instance> <solution> -t <seconds> -seed <int>" << endl; return 2; }
	inFile = argv[1];
	ADAPT_sol = argv[2];
	for (int a = 3; a + 1 < argc; a += 2) {
		string key = argv[a];
		if (key == "-t") ADAPT_T = atof(argv[a + 1]);
		else if (key == "-seed") seed = (unsigned)atoi(argv[a + 1]);
	}

	/*if (argc == 4){
		inFile = argv[1];
		seed = (unsigned)atoi(argv[2]);
		LB = (int)atoi(argv[3]);
	}
	else{
		cout << "Error : the user should input infile to run the program." << endl;
		exit(0);
	}*/
	
	startTime = clock();
	iter = 0;
	//seed = (unsigned)time(NULL);
	srand(seed);
	grand_.seed(seed);
	Read_Data();
	Init();
	cout << fixed << setprecision(3);
	LB = ADAPT_trivial_lb();
	ADAPT_snapshot();
	printf("TRACE %.3f %d\n", (double)(clock() - startTime) / CLOCKS_PER_SEC, ans_makespan); fflush(stdout);


	// clock() reads the process CPU time through a system call (~0.5 us, a sizeable share of an iteration):
	// check the time limit every 64 iterations only (overshoot < 64 iterations, i.e. well under a millisecond)
	bool timeUp = false;
	while (ans_makespan > LB) {
		if ((iter & 63) == 0) {
			double el = (double)(clock() - startTime) / CLOCKS_PER_SEC;
			if (el >= ADAPT_T) break;
			if (!endgame && el >= (1.0 - ENDGAME_FRAC) * ADAPT_T) {
				// offer S1_v5, end game: diversity has no future value any more; search around the best solution only
				endgame = 1;
				Episode_End();
				// sort the pool by cost (best first); the best solution is always in it
				for (int a = 0; a < poolN; a++) for (int b = a + 1; b < poolN; b++) if (poolCost[b] < poolCost[a]) {
					static int tmp[MAXM][MAXN]; int c;
					memcpy(tmp, poolSeq[a], sizeof(tmp)); memcpy(poolSeq[a], poolSeq[b], sizeof(tmp)); memcpy(poolSeq[b], tmp, sizeof(tmp));
					c = poolCost[a]; poolCost[a] = poolCost[b]; poolCost[b] = c;
				}
				if (poolN == 0 || poolCost[0] != ans_makespan) { // safety: polish the best solution itself first
					memcpy(poolSeq[0], ADAPT_best, sizeof(ADAPT_best)); poolCost[0] = ans_makespan; if (poolN == 0) poolN = 1;
				}
				egStart = el; egLen = (ADAPT_T - el) / poolN;
				EG_Begin_Phase(0);
			}
			else if (endgame && egPhase + 1 < poolN && el >= egStart + egLen * (egPhase + 1)) EG_Begin_Phase(egPhase + 1);
		}//N8
	//while (time(NULL)-t0<endTime) {
		const int prevC = this_makespan;
		Tabu_Search();
		if (!endgame) Episode_Track();
		bool anchorUp = false;
		if (endgame && this_makespan < anchorCost) { anchorCost = this_makespan; Copy_Current(anchorSeq); anchorCrit = Crit_Count(); anchorH[0] = hashObj1; anchorH[1] = hashObj2; anchorH[2] = hashObj3; anchorUp = true; }
		else if (endgame && this_makespan == anchorCost) {
			// plateau drift: an equal-cost solution with fewer critical operations becomes the anchor
			int c = Crit_Count();
			if (c <= anchorCrit && (hashObj1 != anchorH[0] || hashObj2 != anchorH[1] || hashObj3 != anchorH[2])) { anchorCrit = c; Copy_Current(anchorSeq); anchorH[0] = hashObj1; anchorH[1] = hashObj2; anchorH[2] = hashObj3; egTieUp++; }
		}
		if (this_makespan < ans_makespan) {//
			kickPend = 0;
			bestTime = (double)(clock() - startTime) / CLOCKS_PER_SEC;
			noImprove = 0;
			ans_makespan = this_makespan;
			bestIter = iter;
			ADAPT_snapshot();
			printf("TRACE %.3f %d\n", bestTime, ans_makespan); fflush(stdout);
			cout << "Find the better solution: " << left << setw(6) << ans_makespan << bestTime << "s iter=" << iter << endl;
		}
		else if (anchorUp) noImprove = 0; // end game: the phase's own best improved
		else {
			noImprove++;
			bool due = (noImprove % tabuDepth == 0);
			// walk: a due kick is postponed while the walk is still descending (its last move lowered the makespan)
			if (!endgame) { if (due) kickPend = 1; due = kickPend && this_makespan >= prevC; }
			if (due) {//		
				kickPend = 0;
				if (endgame) Restore_From(anchorSeq); // end game: every kick starts from the phase's best solution
				Jump_Pit(2, 0);
				if (noImprove >= searchDepth) {//5
					if (!endgame) Jump_Pit(10, 0);
					noImprove = 0;
					if (!endgame) Episode_End();
					H1.clear();
					H2.clear();
					H3.clear();
					lastClear = iter;
				}
			}
		}
		if (iter - lastClear >= searchDepth) { // bound the memory age even while improving
			if (!endgame) Episode_End();
			H1.clear(); H2.clear(); H3.clear();
			lastClear = iter;
		}

		//if(iter%10000==0)cout << "The best found solution: " << left << setw(6) << ans_makespan << bestTime << "s iter=" << bestIter << endl;

		++iter;
	}
	cout << "EGTIE " << egTieUp << endl;
	ADAPT_write(ADAPT_sol);
	cout << inFile << "	" << ans_makespan << "	" << bestTime << "	"<< bestIter<<"	" << seed << endl;
	return 0;
}

