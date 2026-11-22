/*   /\_/\
*   (# ._.)
*   / >  \>
*   CF: a_cedia
*   BOJ: tjrn3712
*/
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
typedef unsigned long long ull;
typedef __int128_t lll;
typedef __uint128_t ulll;
typedef long double ld;
const int INF = 1000000000;
const int mod = 998244353;

// Berlekamp-Massey
// Code by koosaga: https://gist.github.com/koosaga/d4afc4434dbaa348d5bef0d60ac36aa4
ll ipow (ll x, ll p, ll mod) {
	ll ret=1,piv=x;
    x%=mod;
	for (;p;p>>=1) {
		if (p&1) ret=(lll)ret*piv%mod;
		piv=(lll)piv*piv%mod;
	}
	return ret;
}
vector<int> berlekamp_massey(vector<int> x){
	vector<int> ls, cur;
	int lf, ld;
	for(int i=0; i<x.size(); i++){
		ll t = 0;
		for(int j=0; j<cur.size(); j++){
			t = (t + 1ll * x[i-j-1] * cur[j]) % mod;
		}
		if((t - x[i]) % mod == 0) continue;
		if(cur.empty()){
			cur.resize(i+1);
			lf = i;
			ld = (t - x[i]) % mod;
			continue;
		}
		ll k = -(x[i] - t) * ipow(ld, mod - 2, mod) % mod;
		vector<int> c(i-lf-1);
		c.push_back(k);
		for(auto &j : ls) c.push_back(-j * k % mod);
		if(c.size() < cur.size()) c.resize(cur.size());
		for(int j=0; j<cur.size(); j++){
			c[j] = (c[j] + cur[j]) % mod;
		}
		if(i-lf+(int)ls.size()>=(int)cur.size()){
			tie(ls, lf, ld) = make_tuple(cur, i, (t - x[i]) % mod);
		}
		cur = c;
	}
	for(auto &i : cur) i = (i % mod + mod) % mod;
	return cur;
}
int get_nth(vector<int> rec, vector<int> dp, ll n){
	int m = rec.size();
	vector<int> s(m), t(m);
	s[0] = 1;
	if(m != 1) t[1] = 1;
	else t[0] = rec[0];
	auto mul = [&rec](vector<int> v, vector<int> w){
		int m = v.size();
		vector<int> t(2 * m);
		for(int j=0; j<m; j++){
			for(int k=0; k<m; k++){
				t[j+k] += 1ll * v[j] * w[k] % mod;
				if(t[j+k] >= mod) t[j+k] -= mod;
			}
		}
		for(int j=2*m-1; j>=m; j--){
			for(int k=1; k<=m; k++){
				t[j-k] += 1ll * t[j] * rec[k-1] % mod;
				if(t[j-k] >= mod) t[j-k] -= mod;
			}
		}
		t.resize(m);
		return t;
	};
	while(n){
		if(n & 1) s = mul(s, t);
		t = mul(t, t);
		n >>= 1;
	}
	ll ret = 0;
	for(int i=0; i<m; i++) ret += 1ll * s[i] * dp[i] % mod;
	return ret % mod;
}
int guess_nth_term(vector<int> x, ll n){
	if(n < x.size()) return x[n];
	vector<int> v = berlekamp_massey(x);
	if(v.empty()) return 0;
	return get_nth(v, x, n);
}
struct elem{int x, y, v;}; // A_(x, y) <- v, 0-based. no duplicate please..
vector<int> get_min_poly(int n, vector<elem> M){
	// smallest poly P such that A^i = sum_{j < i} {A^j \times P_j}
	vector<int> rnd1, rnd2;
	mt19937 rng(0x14004);
	auto randint = [&rng](int lb, int ub){
		return uniform_int_distribution<int>(lb, ub)(rng);
	};
	for(int i=0; i<n; i++){
		rnd1.push_back(randint(1, mod - 1));
		rnd2.push_back(randint(1, mod - 1));
	}
	vector<int> gobs;
	for(int i=0; i<2*n+2; i++){
		int tmp = 0;
		for(int j=0; j<n; j++){
			tmp += 1ll * rnd2[j] * rnd1[j] % mod;
			if(tmp >= mod) tmp -= mod;
		}
		gobs.push_back(tmp);
		vector<int> nxt(n);
		for(auto &i : M){
			nxt[i.x] += 1ll * i.v * rnd1[i.y] % mod;
			if(nxt[i.x] >= mod) nxt[i.x] -= mod;
		}
		rnd1 = nxt;
	}
	auto sol = berlekamp_massey(gobs);
	reverse(sol.begin(), sol.end());
	return sol;
}
ll det(int n, vector<elem> M){
	vector<int> rnd;
	mt19937 rng(0x14004);
	auto randint = [&rng](int lb, int ub){
		return uniform_int_distribution<int>(lb, ub)(rng);
	};
	for(int i=0; i<n; i++) rnd.push_back(randint(1, mod - 1));
	for(auto &i : M){
		i.v = 1ll * i.v * rnd[i.y] % mod;
	}
	auto sol = get_min_poly(n, M)[0];
	if(n % 2 == 0) sol = mod - sol;
	for(auto &i : rnd) sol = 1ll * sol * ipow(i, mod - 2, mod) % mod;
	return sol;
}


// Naive Stuffs
/*ll EulerPhiNaive (ll n) {
    lll a=1,b=1;
    vector<ll> facts = Factorize(n);
    set<ll> fs;
    for (ll i: facts) fs.insert(i);
    for (ll i: fs) {
        a*=i-1;
        b*=i;
    }
    return n*(a/b);
}
*/
/*int MobiusFuncNaive (ll n) {
    vector<ll> facts = Factorize(n);
    set<ll> fs;
    for (ll i: facts) {
        if (fs.find(i)==fs.end()) fs.insert(i);
        else return 0;
    }
    return fs.size()&1?-1:1;
}
*/
// dijklmnopqrstra
// Last updated <Unknown>
/*
    for (int i=1; i<=v; i++) d[i]=INF;
    priority_queue<pii, vector<pii>, greater<>> pq;
    pq.push({d[s]=0, s});
    while (pq.size()){
        auto [cdist, u] = pq.top(); pq.pop();
        if (d[u]!=cdist) continue;
        for (auto[v, cost]: graph[u]) {
            if (d[v]<=d[u]+cost) continue;
            pq.push ({d[v]=d[u]+cost, v});
        }
    }
*/

// Struct for Segment-Tree
// SegmentTree<ll>, SegmentTree<vector<ll>>
// Merge-Sort Tree for 
// SegmentTree<vector<int>> seg(a, [](vector<int> x, vector<int> y){vector<int> ret;ret.resize((int)x.size()+(int)y.size());merge(x.begin(), x.end(), y.begin(), y.end(), ret.begin());return ret;}, (vector<int>){});
// Last updated <Unknown>
template <class T> class SegmentTree {
public:
    int N;
    vector<T> tree;
    T identity;
    function<T(const T&, const T&)> merge;

    SegmentTree(const vector<T>& arr, function<T(const T&, const T&)> merge, T identity)
        : identity(identity), merge(merge){
        N = arr.size();
        tree.resize(N<<1,identity);
        for (int i=0;i<N;i++) tree[N+i] = arr[i];
        for (int i=N-1;i>0;i--) tree[i] = merge(tree[i<<1], tree[i<<1|1]);
    }

    // 비가환모노이드는 이거
    void update_index2(int i, T v) {
        for (tree[i+=N]=v;i>1;i>>=1) tree[i>>1] = i&1 ? merge(tree[i^1], tree[i]) : merge(tree[i], tree[i^1]);
    }

    // 가환모노이드는 이거
    void update_index(int i, T v) {
        for (tree[i+=N]=v;i>1;i>>=1) tree[i>>1] = merge(tree[i], tree[i^1]);
    }

    // 비가환모노이드는 이거
    T query2(int l, int r) {
        T res_l = identity;
        T res_r = identity;
        for (l+=N,r+=N+1;l<r;l>>=1,r>>=1){
            if (l&1) res_l = merge(res_l, tree[l++]);
            if (r&1) res_r = merge(tree[--r], res_r);
        }
        return merge(res_l, res_r);
    }

    // 가환모노이드는 이거
    T query(int l, int r){
        T ret=identity;
        for (l+=N,r+=N+1;l<r;l>>=1,r>>=1){
            if (l&1) ret = merge(ret, tree[l++]);
            if (r&1) ret = merge(ret, tree[--r]);
        }
        return ret;
    }
};
/* This is for Merge-Sort Tree
template <class T> class SegmentTree {
    public:
        int N;
        vector<T> tree;
        T identity;
        function<T(const T&, const T&)> merge;
    
        SegmentTree(const vector<T>& arr, function<T(const T&, const T&)> merge, T identity)
            : identity(identity), merge(merge){
            N = arr.size();
            tree.resize(N<<1,identity);
            for (int i=0;i<N;i++) tree[N+i] = arr[i];
            for (int i=N-1;i>0;i--) tree[i] = merge(tree[i<<1], tree[i<<1|1]);
        }
    
        void update_index(int i, T v) {
            for (tree[i+N]=v;i>1;i>>=1) tree[i>>1] = merge(tree[i], tree[i^1]);
        }

        long long query(int l, int r, int now){
            long long ret = 0;
            for (l+=N,r+=N+1;l<r;l>>=1,r>>=1){
                if (l&1) {
                    ret += tree[l].end() - upper_bound(tree[l].begin(), tree[l].end(), now);
                    l++;
                }
                if (r&1) {
                    r--;
                    ret += tree[r].end() - upper_bound(tree[r].begin(), tree[r].end(), now);
                }
            }
            return ret;
        }
    };
*/
/*
struct LazySegmentTree {
    int N;
    vector<ll> seg;
    vector<bool> lazy;

    LazySegmentTree(int n) {
        N=1;
        for (;N<n;N<<=1);
        seg.assign(2*N,0);
        lazy.assign(2*N,0);
    }

    void zero(int i) {
        seg[i]=0;
        lazy[i]=1;
    }

    void Lazy(int i) {
        if (lazy[i]) {
            zero(i<<1);
            zero(i<<1|1);
            lazy[i]=0;
        }
    }

    void zero(int i, int l, int r, int ll, int rr) {
        if (ll>r||rr<l) return;
        if (ll<=l&&r<=rr) {
            zero(i);
            return;
        }

        Lazy(i);
        int m=(l+r)>>1;
        zero(i<<1,l,m,ll,rr);
        zero(i<<1|1,m+1,r,ll,rr);
        seg[i]=(seg[i<<1]+seg[i<<1|1])%MOD;
    }

    void zero(int l, int r) {
        if (l>r) return;
        zero(1,0,N-1,l,r);
    }
    void add(int i, ll v, int p, int l, int r) {
        if (l==r) {
            seg[p]+=v;
            seg[p]%=MOD;
            return;
        }
        Lazy(p);
        int m=(l+r)>>1;
        if (i<=m) add(i,v,p<<1,l,m);
        else add(i,v,p<<1|1,m+1,r);
        seg[p]=(seg[p<<1]+seg[p<<1|1])%MOD;
    }
    void add(int i, ll v) {
        add(i,v,1,0,N-1);
    }
};
*/
// Not Complete Code
// Last updated <Unknown>
template <class T> class LazySegmentTree {
    public:
    int N;
    vector<T> tree;
    vector<T> segLen;
    vector<T> lazy;
    vector<bool> isLazy;
    T identity;
    T Uidentity;
    function<T(const T&, const T&)> merge;
    function<T(const T&, const T&)> Umerge;

    LazySegmentTree(const vector<T>& arr, function<T(const T&, const T&)> merge, function<T(const T&, const T&)> Umerge, T identity, T Uidentity)
    : identity(identity), merge(merge), Umerge(Umerge), Uidentity(Uidentity){
        N = arr.size();
        tree.resize(N<<1, identity);
        segLen.resize(N<<1, 1);
        lazy.resize(N<<1, Uidentity);
        isLazy.resize(N, false);
        for (int i=0;i<N;i++) tree[N+i] = arr[i];
        for (int i=N-1;i>0;i--) {
            tree[i] = merge(tree[i<<1], tree[i<<1|1]);
            segLen[i] = segLen[i<<1]+segLen[i<<1|1];
        }
    }

    void update(int l, int r, T v){
        for (l+=N,r+=N;l<r;l>>=1,r>>=1){
            if (l&1) {
                tree[l++] = Umerge(tree[l], v);
                for (int i=l<<1;i>1;i<<=1){
                    if (!isLazy[i]){
                        isLazy[i] = true;
                        lazy[i] = Umerge(lazy[i], v);
                    }
                }
            }
            if (~r&1) {
                tree[r--] = Umerge(tree[r], v);
                for (int i=r<<1;i>1;i<<=1){
                    if (!isLazy[i]){
                        isLazy[i] = true;
                        lazy[i] = Umerge(lazy[i], v);
                    }
                }
            }
        }
    }

    T query(int l, int r){
        int L=l,R=r;
        T res_l = identity;
        T res_r = identity;
        for (l+=N,r+=N;l<r;l>>=1,r>>=1){
            if (l&1) {
                if (isLazy[l]) {
                    tree[l]=Umerge(tree[l], lazy[r]);
                    lazy[l] = Uidentity;
                    isLazy[l] = false;
                }
                res_l = merge(res_l, tree[l++]);
            }
            if (~r&1) {
                if (isLazy[r]) {
                    tree[r]=Umerge(tree[l], lazy[r]);
                    lazy[r] = Uidentity;
                    isLazy[r] = false;
                }
                res_r = merge(tree[r--], res_r);
            }
        }
        
        return merge(res_l, res_r);
    }
};

// Edge Struct for Push-Relabel
template <class T> struct Edge {
    int from, to, index;
    T cap, flow;

    Edge(int from, int to, T cap, T flow, int index): from(from), to(to), cap(cap), flow(flow), index(index) {}
};
// Push-Relable Structure
// PushRelabel<ll> p(N), p.add_edge(from, to, cap), p.flow(S, T)
// Code refered to Corei13: https://codeforces.com/blog/entry/14378
template <class T> struct PushRelabel {
    int n;
    vector <vector <Edge <T>>> adj;
    vector <T> excess;
    vector <int> dist, count;
    vector <bool> active;
    vector <vector <int>> B;
    int b;
    queue <int> Q;

    PushRelabel (int n): n(n), adj(n) {}

    void add_edge (int from, int to, int cap) {
        adj[from].push_back(Edge <T>(from, to, cap, 0, adj[to].size()));
        if (from == to) adj[from].back().index++;
        adj[to].push_back(Edge <T>(to, from, 0, 0, adj[from].size()-1));

    }

    void Enqueue (int v) {
        if (!active[v] && excess[v] > 0 && dist[v] < n) {
            active[v] = true;
            B[dist[v]].push_back(v);
            b = max(b, dist[v]);
        }
    }

    void Push (Edge <T> &e) {
        T amt = min(excess[e.from], e.cap - e.flow);
        if (dist[e.from] == dist[e.to] + 1 && amt > T(0)) {
            e.flow += amt;
            adj[e.to][e.index].flow -= amt;
            excess[e.to] += amt;    
            excess[e.from] -= amt;
            Enqueue(e.to);
        }
    }

    void Gap (int k) {
        for (int v = 0; v < n; v++) if (dist[v] >= k) {
            count[dist[v]]--;
            dist[v] = max(dist[v], n);
            count[dist[v]]++;
            Enqueue(v);
        }
    }

    void Relabel (int v) {
        count[dist[v]]--;
        dist[v] = n;
        for (auto e: adj[v]) if (e.cap - e.flow > 0) dist[v] = min(dist[v], dist[e.to] + 1);
        count[dist[v]]++;
        Enqueue(v);
    }

    void Discharge(int v) {
        for (auto &e: adj[v]) {
            if (excess[v] > 0) Push(e);
            else break;
        }

        if (excess[v] > 0) {
            if (count[dist[v]] == 1) Gap(dist[v]); 
            else Relabel(v);
        }
    }

    T flow (int s, int t) {
        dist = vector <int>(n, 0), excess = vector<T>(n, 0), count = vector <int>(n + 1, 0), active = vector <bool>(n, false), B = vector <vector <int>>(n), b = 0;
        
        for (auto &e: adj[s]) excess[s] += e.cap;

        count[0] = n;
        Enqueue(s);
        active[t] = true;
        
        while (b >= 0) {
            if (!B[b].empty()) {
                int v = B[b].back();
                B[b].pop_back();
                active[v] = false;
                Discharge(v);
            } else b--;
        }
        return excess[t];
    }

    T GetMinCut (int s, int t, vector <int> &cut);
};

// Edge Struct for Dinic
template <class T> struct FlowEdge {
    int v, u;
    T cap, flow = 0;
    
    FlowEdge(int v, int u, T cap): v(v), u(u), cap(cap) {}
};
// Dinic Structure
// Dinic<ll> d(N), d.add_edge(from, to, cap), d.flow(S, T)
// Code from cp-algorithms: https://cp-algorithms.com/graph/dinic.html
template <class T> struct Dinic {
    const long long flow_inf = 1e18;
    vector<FlowEdge<ll>> edges;
    vector<vector<ll>> adj;
    ll n, m=0;
    ll s, t;
    vector<ll> level, ptr;
    queue<ll> q;

    Dinic(ll n): n(n) {
        adj.resize(n);
        level.resize(n);
        ptr.resize(n);
    }

    void add_edge(ll v, ll u, long long cap = 1) {
        edges.emplace_back(v, u, cap);
        edges.emplace_back(u, v, 0);
        adj[v].push_back(m);
        adj[u].push_back(m+1);
        m+=2;
    }

    bool bfs(auto t) {
        while (!q.empty()) {
            ll v = q.front();
            q.pop();
            for (int id: adj[v]) {
                if (edges[id].cap == edges[id].flow) continue;
                if (level[edges[id].u] != -1) continue;
                level[edges[id].u] = level[v]+1;
                q.push(edges[id].u);
            }
        }
        return level[t]!=-1;
    }

    long long dfs(ll v, long long pushed, auto t) {
        if (pushed == 0) return 0;
        if (v == t) return pushed;

        for (ll& cid=ptr[v]; cid<(int)adj[v].size(); cid++) {
            ll id = adj[v][cid];
            ll u = edges[id].u;
            if (level[v]+1 != level[u]) continue;

            long long tr = dfs(u, min(pushed, edges[id].cap-edges[id].flow), t);
            if (tr == 0) continue;

            edges[id].flow += tr;
            edges[id^1].flow -= tr;
            return tr;
        }
        return 0;
    }

    long long flow(auto s, auto t) {
        long long f = 0;
        while (true) {
            fill(level.begin(), level.end(), -1);
            level[s] = 0;
            q.push(s);
            if (!bfs(t)) break;

            fill(ptr.begin(), ptr.end(), 0);
            while (long long pushed = dfs(s, flow_inf, t)) f += pushed;
        }
        return f;
    }
};

// HLD
// Not complete Code
/*
int pv;
Node *ptr[101010];
struct Node {
    Node *p, *top;
    pair<Node*, int> w = {p, 0};
    int k,sz=1,dep=1,in=pv,out=pv;
    vector<Node*> c;
    Node (int k): k(k) {ptr[k]=this;}
};
void dfs1 (int v=1) {
    ptr[v]->sz=1;
    for (auto &i:ptr[v]->c) {
        i->dep = ptr[v]->dep+1;i->p=ptr[v];
        dfs1(i->k); ptr[v]->sz+=i->sz;
        if (i->sz>ptr[v]->c[0]->sz) swap(i,ptr[v]->c[0]);
    }
}
void dfs2 (int v=1) {
    ptr[v]->in=++pv;
    for (auto i:ptr[v]->c) {
        i->top=i==ptr[v]->c[0]?ptr[v]->top:i;
        dfs2(i->k);
    }
    ptr[v]->out=pv;
}
*/

// Bipartate-Matching O(N³)
// bipartate_matching(간선벡터, 노드벡터 A, 노트벡터 B, 1 (현재 노드번호 a in A), 방문벡터)
bool bipartate_matching(auto adj, auto A, auto B, auto a, auto visited) {
    visited[a] = true;
    for (auto &b: adj[a]) {
        if (B[b] == -1 or !visited[B[b]] and bipartate_matching(adj, A, B, B[b], visited)) {
            A[a] = b; B[b] = a;
            return true;
        }
    }
    return false;
}

// ccw
// a -> b -> c의 방향성을 알려줌
struct Point {ll x,y;};
ll ccw(Point a, Point b, Point c) {
    return (b.x-a.x)*(c.y-a.y)-(b.y-a.y)*(c.x-a.x);
}
ll ccw4 (Point a, Point b, Point c, Point d) {
    return (b.x-a.x)*(d.y-c.y)-(b.y-a.y)*(d.x-c.x);
}
Point pivot = {-100000,-100000}; // 알아서 수정 이후 정렬하셈요
bool cmp (Point a, Point b) {
    ll c = ccw(pivot,a,b);
    if (c==0) {
        if (a.y==b.y) return a.x<b.x;
        return a.y<b.y;
    }
    return c>0;
}
ll dist2 (Point a, Point b) {
    return (a.x-b.x)*(a.x-b.x)+(a.y-b.y)*(a.y-b.y);
}
void cHull (vector<Point> &a, vector<Point> &h) {
    int n = a.size();
    int x=-100000,y=-100000,idx=0;
    for (int i=0;i<n;i++) if (a[i].y<a[idx].y||(a[i].y==a[idx].y&&a[i].x<a[idx].x)) idx=i;

    swap(a[idx],a[0]);
    pivot=a[0];
    sort(a.begin()+1,a.end(),cmp);
    h.push_back(a[0]);
    h.push_back(a[1]);
    for (int i=2;i<n;i++) {
        for (;h.size()>=2&&ccw(h[h.size()-2],h.back(),a[i])<=0;) h.pop_back();
        h.push_back(a[i]);
    }
}

ll rotCalipers (vector<Point> &h, Point &p1, Point &p2) {
    int n=h.size();
    ll d = -9;
    ll dd;
    int j=1;
    p1=h[0],p2=h[1];
    for (int i=0;i<n;i++) {
        int ni=(i+1)%n;
        for (;;) {
            int nj=(j+1)%n;
            if (llabs(ccw(h[i],h[ni],h[j]))<llabs(ccw(h[i],h[ni],h[nj]))) j=nj;
            else break;
        }
        dd=dist2(h[i],h[j]);
        if (dd>d) d=dd,p1=h[i],p2=h[j];
        dd=dist2(h[ni],h[j]);
        if (dd>d) d=dd,p1=h[ni],p2=h[j];
    }
    return d;
}

// Intersection Check for Segments
// ab와 cd가 교차하는가?
bool line_seg_intersection(auto a, auto b, auto c, auto d) {
    ll ab = ccw(a,b,c)*ccw(a,b,d);
    ll cd = ccw(c,d,a)*ccw(c,d,b);
    if (!ab and !cd) {
        if (a > b) swap(a, b);
        if (c > d) swap(c, d);
        return !(b<c and d<a);
    }
    return ab<=0 and cd<=0;
}

// Area of Polygon
// vertices: array of vert.
ld shoelace_area(auto vertices) {
    ll n = (ll)vertices.size();
    ld area = 0;
    for (int i=0; i<n; i++) {
        ll x_i = vertices[i].first, y_i = vertices[i].second;
        ll x_next = vertices[(i+1)%n].first, y_next = vertices[(i+1%n)].second;
        area += (ld)(x_i*y_next) - (ld)(x_next*y_i);
    }
    return abs(area)/(ld)2.0;
}

// Splay Tree, LCT
// Last updated 2025-11-15-02-28-55 UTC+9.
struct SplayTree {
    struct Node {
        Node *l,*r,*p;
        int key=0;
        int cnt=1;
        ll sum=0, value=0, lazy=0, min=LLONG_MAX, max=LLONG_MIN;
        bool inv=false;
    };
    int size=0;
    Node *tree = NULL;
    // Node *ptr[101010];

    void Rotate (Node *x) {
        Node* p = x->p;
        Node* b = NULL;

        Lazy(p);
        Lazy(x);
        
        if (!p) return;
        if (x==p->l) {
            p->l = b = x->r;
            x->r = p;
        } else {
            p->r = b = x->l;
            x->l = p;
        }

        x->p = p->p;
        p->p = x;

        if (b) b->p = p;
        (x->p?p==x->p->l?x->p->l:x->p->r:tree) = x;

        Update(p);
        Update(x);
    }
    void Splay (Node* x) {
        Lazy(x);
        for (;x->p;) {
            Node* p = x->p;
            Node* g = p->p;

            if (g) {
                if ((x==p->l) == (p==g->l)) Rotate(p);
                else Rotate(x);
            }
            Rotate(x);
        }
    }
    
    void Insert (int key) {
        size++;
        Node* p = tree;
        Node** pp;
        if (!p) {
            Node* x = new Node;
            tree = x;
            x->l=x->r=x->p=NULL;
            x->key = key;
            return;
        }
        for (;1;) {
            if (p->key == key) return;
            if (p->key > key) {
                if (!p->l) {
                    pp = &p->l;
                    break;
                }
                p = p->l;
            } else {
                if (!p->r) {
                    pp = &p->r;
                    break;
                }
                p = p->r;
            }
        }
        Node* x = new Node();
        *pp = x;
        x->l=x->r=NULL;
        x->p = p;
        x->key = key;

        Splay(x);
    }
    bool Find (int key) {
        Node* p = tree;
        if (!p) return false;
        for (;p;) {
            if (p->key==key) break;
            if (p->key > key) {
                if (!p->l) break;
                p = p->l;
            } else {
                if (!p->r) break;
                p = p->r;
            }
        }
        Splay(p);
        return key==p->key;
    }
    void Delete (int key) {
        if (!Find(key)) return;
        size--;
        Node* p = tree;
        if (p->l&&p->r) {
            tree = p->l;
            tree->p = NULL;

            Node* x = tree;
            for (;x->r;) x = x->r;
            x->r = p->r;
            p->r->p = x;
            delete p;
            return;
        }

        if (p->l) {
            tree = p->l;
            tree->p = NULL;
            delete p;
            return;
        }

        if (p->r) {
            tree = p->r;
            tree->p = NULL;
            delete p;
            return;
        }

        delete p;
        tree = NULL;
    }

    void Update (Node *x) {
        x->cnt = 1;
        x->sum = x->value;
        x->min = x->value;
        x->max = x->value;
        if (x->l) {
            Lazy(x->l);
            x->sum += x->l->sum;
            x->cnt += x->l->cnt;
            x->min = min(x->min, x->l->min);
            x->max = max(x->max, x->l->max);
        }
        if (x->r) {
            Lazy(x->r);
            x->sum += x->r->sum;
            x->cnt += x->r->cnt;
            x->min = min(x->min, x->r->min);
            x->max = max(x->max, x->r->max);
        }
    }
    void Find_kth (int k) {
        Node* x = tree;
        for (;1;) {
            for (;x->l && x->l->cnt>k;) {
                x = x->l;
                Lazy(x);
            }
            if (x->l) k -= x->l->cnt;
            if (!k--) break;
            x = x->r;
            Lazy(x);
        }
        Splay(x);
    }
    void Init (int n) {
        n+=2;
        size = n;
        Node* x;
        tree = x = new Node;
        // ptr[0] = x;
        x->l=x->r=x->p=NULL;
        x->cnt = n;
        x->value=0;
        Update(x);
        for (int i=1;i<n;i++) {
            x->r = new Node;
            // ptr[i] = x->r;
            x->r->p = x;
            x = x->r;
            x->l = x->r = NULL;
            x->cnt = n-i;
            x->value = 0;
            Update(x);
        }
    }
    void Add1 (int i, ll v) {
        Find_kth(i);
        tree->sum += v;
        tree->value += v;
    }
    void Add2 (int l, int r, ll v) {
        Interval(l,r);
        Node* x = tree->r->l;
        x->sum += x->cnt*v;
        x->lazy += v;
    }
    void Interval (int l, int r) {
        Find_kth(l-1);
        Node *x = tree;
        tree = x->r;
        tree->p = NULL;
        Find_kth(r-l+1);
        x->r = tree;
        tree->p = x;
        tree = x;
    }
    ll Sum (int l, int r) {
        Interval(l, r);
        return tree->r->l->sum;
    }
    void Lazy(Node *x) {
        if (x->lazy) {
            x->value += x->lazy;
            if (x->l) {
                x->l->lazy += x->lazy;
                x->l->sum += x->l->cnt*x->lazy;
            }
            if (x->r) {
                x->r->lazy += x->lazy;
                x->r->sum += x->r->cnt*x->lazy;
            }
            x->lazy = 0;
        }
        if (x->inv) {
            swap(x->l,x->r);
            x->inv = false;
            if (x->l) x->l->inv^=1;
            if (x->r) x->r->inv^=1;
        }

    }
    void Reverse (int l, int r) {
        Interval(l,r);
        Node* x = tree->r->l;
        x->inv = !x->inv;
        for (;x;x=x->p) Update(x);
    }
    void Shift (int l, int r, int k) {
        k = (k%(r-l+1)+r-l+1)%(r-l+1);
        if (!k) return;
        Reverse(l,r);
        Reverse(l,l+k-1);
        Reverse(l+k,r);
    }
    /*int Index (int value) {
        Splay(ptr[value]);
        return tree->l?tree->l->cnt:0;
    }*/

    void InsertKth (int k, int v) {
        size++;
        Find_kth(k);
        Node *x = new Node;
        tree->cnt++;
        x->l = tree->l;
        x->r = NULL;
        x->l->p = x;
        x->p = tree;
        tree->l = x;
        x->cnt = x->l->cnt+1;
        x->value = v;
        Update(x);
        Update(x->p);
        Splay(x);
    }
    void DeleteKth (int k) {
        if (size<=2) return;
        size--;
        Find_kth(k);
        Node* p = tree;
        if (p->l&&p->r) {
            int temp = tree->r->cnt;
            tree = p->l;
            tree->p = NULL;

            Node* x = tree;
            for (;x->r;) {
                x->cnt += temp;
                x = x->r;
            }
            x->r = p->r;
            p->r->p = x;
            delete p;
            for (;x->p;) {
                Update(x);
                x = x->p;
            }
            return;
        }

        if (p->l) {
            tree = p->l;
            tree->p = NULL;
            delete p;
            return;
        }

        if (p->r) {
            tree = p->r;
            tree->p = NULL;
            delete p;
            return;
        }

        delete p;
        tree = NULL;
    }
};

// How to Use: https://www.acmicpc.net/source/98510941
struct LinkCutTree {
    struct Node {
        Node *l=NULL,*r=NULL,*p=NULL;
        ll sz=1,value=0,sum=0,lazy=0;
        bool inv=false;
    };
    LinkCutTree::Node ptr[123456];
    bool isRoot (Node* x) {
        return !x->p||(x!=x->p->l&&x!=x->p->r);
    }
    bool isLeft (Node* x) {
        return x==x->p->l;
    }

    void Update (Node* x) {
        x->sz = 1, x->sum = x->value;
        if (x->l) x->sz+=x->l->sz, x->sum+=x->l->sum;
        if (x->r) x->sz+=x->r->sz, x->sum+=x->r->sum;
    }
    void Update (Node* x, ll v) {
        x->value =  v;
        Update(x);
    }
    void Rotate (Node* x) {
        if (isLeft(x)) {
            if (x->r) x->r->p = x->p;
            x->p->l = x->r;
            x->r = x->p;
        } else {
            if (x->l) x->l->p = x->p;
            x->p->r = x->l;
            x->l = x->p;
        }
        if (!isRoot(x->p)) (isLeft(x->p)?x->p->p->l:x->p->p->r) = x;
        Node* t = x->p;
        x->p = t->p;
        t->p = x;
        Update(t);
        Update(x);
    }
    void Splay (Node* x) {
        Push(x);
        for (;!isRoot(x);) {
            Node* p = x->p;
            Node* g = p->p;
            if (!isRoot(p)) Lazy(g);
            Lazy(p);
            Lazy(x);
            if (!isRoot(x->p)) {
                if (isLeft(x)==isLeft(p)) Rotate(p);
                else Rotate(x);
            }
            Rotate(x);
        }
        Update(x);
    }
    void Apply (Node*x, ll v) {
        if (!x) return;
        x->value+=v;
        x->sum+=v*x->sz;
        x->lazy+=v;
    }
    void Lazy (Node* x) {
        if (!x) return;
        if (x->lazy) {
            if (x->l) Apply(x->l,x->lazy);
            if (x->r) Apply(x->r,x->lazy);
        }
        x->lazy=0;
        if (x->inv) {
            swap(x->l, x->r);
            if (x->l) x->l->inv^=1;
            if (x->r) x->r->inv^=1;
            x->inv^=1;
        }
    }

    void Push (Node* x) {
        static Node* st[303030];
        int top=0;
        Node*y = x;
        st[top++]=y;
        for (;!isRoot(y);st[top++]=y) y=y->p;
        for (;top;) Lazy(st[--top]);
    }
    Node* Access(Node* x) {
        Node* t = NULL;
        for (Node*y = x;y;y=y->p) {
            Splay(y);
            y->r=t;
            Update(y);
            t=y;
        }
        Splay(x);
        return t;
    }

    void Link (Node* u, Node* v) {
        MakeRoot(u);
        if (FindRoot(v)!=u) u->p=v;
    }
    void Link (int p, int c) {
        Link(ptr+p, ptr+c);
    }
    void Cut (Node* p) {
        Access(p);
        if (p->l) {
            p->l->p=NULL;
            p->l=NULL;
            Update(p);
        }
    }
    void Cut (int p) {
        Cut(ptr+p);
    }
    Node* FindRoot (Node* x) {
        Access(x);
        for (;x->l;) {
            x=x->l;
            Lazy(x);
        }
        Access(x);
        return x;
    }
    Node* FindRoot (int x) {
        return FindRoot(&ptr[x]);
    }
    Node* FindParent (Node* x) {
        Access(x);
        if (!x->l) return NULL;
        x=x->l;
        Lazy(x);
        for (;x->l;) {
            x=x->r;
            Lazy(x);
        }
        Access(x);
        return x;
    }
    int Depth (Node* x) {
        Access(x);
        return x->l?x->l->sz:0;
    }
    Node* LCA (Node* u, Node* v) {
        Access(u);
        Access(v);
        Splay(u);
        return u->p?u->p:u;
    }
    int LCA (int u, int v) {
        return LCA(ptr+u, ptr+v)-ptr;
    }
    void MakeRoot (Node* x) {
        Access(x);
        x->inv^=1;
        Lazy(x);
    }
    ll VQuery (Node* x, Node* y) {
        Node* t = LCA(x, y);
        ll ret = t->value;

        Access(x);
        Splay(t);
        if (t->r) ret=ret+t->r->sum;
        
        Access(y);
        Splay(t);
        if (t->r) ret=ret+t->r->sum;
        return ret;
    }
    ll VQuery (int x, int y) {
        return VQuery(ptr+x,ptr+y);
    }
    void VUpdate (Node* x, ll v) {
        Splay(x);
        x->value = v;
        Update(x);
    }
    void VUpdate (int i, ll v) {
        VUpdate(ptr+i,v);
    }
    void PUpdate (Node* x, Node* y, ll v) {
        Node* root = FindRoot(x);
        MakeRoot(x);
        Access(y);
        
        // x, y를 chain 하나로 묶어줌요
        Splay(x);
        x->lazy+=v;
        Lazy(x);
        
        MakeRoot(root); // rerooting
    }
    ll PQuery (Node* x, Node* y) {
        Node* l = LCA (x, y);
        ll ret = l->value;
        Access(x);
        Splay(l);

        if (l->r) ret += l->r->sum;
        Access(y);
        Splay(l);

        if (l->r) ret += l->r->sum;
        return ret;
    }

}tree;

struct WeightBalancedTree {
    struct Node {
        ll lazy;
        int l,r,cnt;
        ll sum;
    }pool[202020];

    int piv=0;
    int Join (int l, int r) {
        int n = ++piv;
        pool[n] = {0,l,r,pool[l].cnt+pool[r].cnt,pool[l].sum+pool[r].sum};
        return n;
    }

    int Init (int s, int e) {
        if (s+1==e) {
            int x;
            cin>>x;
            pool[e] = {0,0,0,1,x};
            return e;
        }
        int m = (s+e)>>1;
        int l = Init(s,m);
        int r = Init(m,e);
        return Join(l,r);
    }

    bool isBalanced (int u, int v, int a = 4) {
        u = pool[u].cnt;
        v = pool[v].cnt;
        return u<=a*v&&v<=a*u;
    }
    bool isBalanced_cnt (int u, int v, int a = 4) {
        return u<=a*v&&v<=a*u;
    }
    
    void Lazy (int x) {
        if (pool[x].lazy) {
            if (pool[x].l) {
                pool[++piv] = pool[pool[x].l];
                pool[x].l = piv;
                pool[pool[x].l].lazy += pool[x].lazy;
			    pool[pool[x].l].sum += pool[x].lazy*pool[pool[x].l].cnt;
            }
            if (pool[x].r) {
                pool[++piv] = pool[pool[x].r];
                pool[x].r = piv;
                pool[pool[x].r].lazy += pool[x].lazy;
			    pool[pool[x].r].sum += pool[x].lazy*pool[pool[x].r].cnt;
            }
            pool[x].lazy = 0;
        }
    }

    int merge (int l, int r) {
        if (!l) return r;
        if (!r) return l;
        if (isBalanced(l,r)) return Join(l,r);
        if (pool[l].cnt>pool[r].cnt) {
            Lazy(l);
            int ll = pool[l].l;
            int lr = pool[l].r;
            if (isBalanced(ll,lr)) Join(ll,lr);
            if (isBalanced(ll,pool[lr].l)&&isBalanced_cnt(pool[ll].cnt+pool[pool[lr].l].cnt,pool[pool[lr].r].cnt)) return Join(Join(ll,pool[lr].l),pool[lr].r);
    
        }
    }
};

// O(log N) Find
struct UnionFind {
    int p[444444];
    stack<tuple<int,int,int>> s;
    UnionFind () {
        memset(p, -1, sizeof(p));
    }
    int find (int x) {
        if (p[x]<0) return x;
        return find(p[x]);
    }
    bool uni (int x, int y) {
        x=find(x),y=find(y);
        if (x==y) return 0;
        if (p[x]<p[y]) swap(x,y);
        s.push({x,y,p[x]});
        p[y]+=p[x];
        p[x]=y;
        return 1;
    }
    void rollback () {
        int x = get<0>(s.top()), y = get<1>(s.top()), sz = get<2>(s.top());
        p[y] -= sz;
        p[x] = sz;
        s.pop();
    }
};
// Amortized O(1) Find (for PS, CP range)
struct UnionFindAmortized {
    int p[444444]={};
    int find (int x) {
        if (!p[x]) return x;
        p[x] = find(p[x]);
        return p[x];
    }
    bool uni (int x, int y) {
        x=find(x),y=find(y);
        if (x==y) return 0;
        p[x]=y; return 1;
    }
};

// Useful Stuffs
bool isComposite (ll n, ll a, ll d, ll s) {
    ll x = ipow(a, d, n);
    if (x==1||x==n-1) return false;
    for (ll r=1;r<s;r++) {
        x = (lll)x*x%n;
        if (x==n-1) return false;
    }
    return true;
}
ll llgcd(ll a, ll b) {
    if (a<b) swap(a,b);
    ll r;
    for (;b;) {
        r=a%b;
        a=b;
        b=r;
    }
    return a;
}

// Miller-Rabin Prime Check
mt19937_64 rng(0x94949);
uniform_int_distribution<ll> r{};
bool MillerRabin (ll n, ll a) {
    if (!(n%a)) return 0;
	ll d = n-1;
	for (;;d>>=1) {
		ll tmp = ipow(a, d, n);
		if (d&1) return (tmp!=1&&tmp!=n-1);
		else if (tmp==n-1) return 0;
	}
}
bool isPrime (ll n) {
    for (ll i: {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}) {
		if (n==i) return 1;
		if (n>40&&MillerRabin(n,i)) return 0;
	}
	if (n<=40) return 0;
	return 1;
}

// Pollard-Rho (needs Miller-Rabin)
ll f (ll x, ll n, ll c) {
    return (c+(lll)x*x%n)%n;
}
void PollardRho (ll n, vector<ll> &v) {
    if (n==1) return;
    if (~n&1) {v.push_back(2);PollardRho(n>>1,v);return;}
    if (isPrime(n)) {v.push_back(n);return;}
    ll x,y,c;
    for (;;) {
        x = r(rng)%(n-2)+2;
        y = x;
        c = r(rng)%20+1;
        do {
            x = f(x,n,c);
            y = f(f(y,n,c),n,c);
        } while (llgcd(llabs(x-y),n)==1);
        if (x!=y) break;
    }
    ll a = llgcd(llabs(x-y),n);
    PollardRho(a,v);
    PollardRho(n/a,v);
}
vector<ll> Factorize (ll n) {
    vector<ll> ret;
    PollardRho(n, ret);
    sort(ret.begin(),ret.end());
    return ret;
}

// FFT Recursive
/* Input stuffs
f: Coefficient of Polynomial
w: Principal n-th of Unity

If you want to know about w, go https://en.wikipedia.org/wiki/Root_of_unity.
*/
/* How to do polynomial multiplying:
1. Find N. Where N be min. of pow(2, p) >= max(len of Polynomials)
2. Get w (Principal n-th root of Unity). w = cos(2*pi/N) + i*sin(2*pi/N), that is, complex<double> w(cos(2*pi/n) + i*sin(2*pi/n)).
3. Get DFT of two polynomials. FFT(a, w); FFT(b, w);
4. Multiply each coefficients. (with for-repitition) Let multiplied vector be c.
5. Do IDFT. 
-> FFT(c, complex<double>(w.real(), -w.imag()));
   and, divide each coefficients by complex<double>(n, 0). that is, just n.
*/
// Last updated 2025-09-08-14-26-38 UTC+9.
void FFT (vector<complex<double>> &f, complex<double> w) {
    int n = (int)f.size();
    if (n==1) return;
    vector<complex<double>> even(n>>1), odd(n>>1);
    for (int i=0;i<n;i++) {
        if (i&1) odd[i>>1] = f[i];
        else even[i>>1] = f[i];
    }
    FFT(odd, w*w), FFT(even, w*w);

    complex<double> t(1, 0);
    n >>= 1;
    for (int i=0;i<n;i++) {
        f[i] = even[i] + t*odd[i];
        f[i+n] = even[i] - t*odd[i];
        t *= w;
    }
}


void solve() {
    int n,q,c,l;
    ll r;
    cin>>n>>q;
    vector<ll> a(n);
    for (int i=0;i<n;i++) cin>>a[i];
    
    SegmentTree<ll> seg(a, [](ll x, ll y){return x+y;},0);
    for (;q--;) {
        cin>>c>>l>>r;
        l--;
        if (c==1) {
            seg.update_index(l,r);
        } else {
            r--;
            cout<<seg.query(l,r)<<'\n';
        }
    }
}
int main(){
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    cout.tie(NULL);

    int t=1; //cin>>t;
    for (;t--;) solve();
}