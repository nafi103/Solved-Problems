#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define aint(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
vector<int>head;
struct S {
    bool mt;
    int zz,oz,zo,oo;

    S(){
        mt = true;
    }

    S (long long val) {
        mt = false;
        zz = 0;
        zo = oz = -inf;
        oo = val;
    }
};

S combine(const S &a,const S &b)
{
    if(a.mt)
        return b;
    if(b.mt)
        return a;
    S res;
    res.mt = false;
    res.zz = max({ a.zz + b.zz, a.zo + b.zz, a.zz + b.oz });
    res.zo = max({ a.zz + b.zo, a.zo + b.zo, a.zz + b.oo });
    res.oz = max({ a.oz + b.zz, a.oo + b.zz, a.oz + b.oz });
    res.oo = max({ a.oz + b.zo, a.oo + b.zo, a.oz + b.oo });
    return res;
}

struct Segment_Tree{
    int n;
    vector<S>st;

    Segment_Tree(int _n){
        n = _n;
        st.resize(4*n);
    }

    void update(int node, int b, int e, int &id, int &value){
        if(e<id or b>id) return;
        if(b==e){
            st[node] = S(value);
            return;
        }
        int mid = (b+e)/2,left = 2*node, right = 2*node+1;
        update(left, b, mid,id,value);
        update(right, mid+1,e,id,value);
        st[node] = combine(st[left],st[right]);
    }
    
    S query(int node, int b, int e, int &l, int &r){
        if(e<l or b>r) return S();
        if(b>=l and e<=r){
            return st[node];
        }
        int mid = (b+e)/2, left = 2*node, right = 2*node+1;
        S ql = query(left,b,mid,l,r), qr = query(right,mid+1,e,l,r);
        return combine(ql, qr);
    }
};



struct HLD {
    int n, cur_pos = 0, mx;
    vector<int> arr, size, depth, heavy, pos;
    vector<vector<int>> adj, parents;
    Segment_Tree segtree;
    HLD(int n)
        : n(n)
        , mx(log2(n)+5)
        , arr(n + 1)
        , parents(mx,vector<int>(n+1,-1))
        , size(n + 1)
        , depth(n + 1)
        , heavy(n + 1, 0)
        , pos(n + 1)
        , adj(n + 1)
        , segtree(Segment_Tree(n))
    {
    }
    void add_edge(int u, int v)
    {
        adj[u].push_back(v), adj[v].push_back(u);
    }
    void dfs(int u, int p)
    {
        parents[0][u] = p;
        size[u] = 1;
        int max_sz = 0;
        for (int v : adj[u]) {
            if (v == p)
                continue;
            depth[v] = depth[u] + 1;
            dfs(v, u);
            size[u] += size[v];
            if (size[v] > max_sz) {
                max_sz = size[v], heavy[u] = v;
            }
        }
    }

    void decompose(int u, int h)
    {
        head[u] = h;
        pos[u] = ++cur_pos;
        segtree.update(1,1,n,pos[u], arr[u]);
        if (heavy[u])
            decompose(heavy[u], h);
        for (int v : adj[u])
            if (v != parents[0][u] && v != heavy[u])
                decompose(v, v);
    }

    void go(){
        dfs(1, 0);
        for(int i = 1; i<mx; i++){
            for(int j = 1; j<=n; j++){
                int prevParent = parents[i-1][j];
                if(prevParent!=-1)  parents[i][j] = parents[i-1][prevParent];
            }
        }
        decompose(1, 1);
    }
    int kthParent(int a, int k){
        for(int i = 0; i<mx; i++){
            if(a==-1) return a;
            if(k&(1<<i)) a = parents[i][a];
        }
        return a;
    }

    int lca(int a, int b){
        if(depth[a]>depth[b]){
            a = kthParent(a, depth[a] - depth[b]);
        }else{
            b = kthParent(b, depth[b] - depth[a]);
        }
        if(a==b) return a;
        for(int i = mx-1; i>=0; i--){
            if(parents[i][a]!=parents[i][b]){
                a = parents[i][a];
                b = parents[i][b];
            }
        }
        return parents[0][a];
    }

    S path_ans(int a, int b){
        if(a==b)
            return segtree.query(1,1,n,a,b);
        bool lca_taken = false;
        int LCA = lca(a,b);
        S resl, resr;
        while(head[a] != head[LCA]){
            S up = segtree.query(1,1,n,pos[head[a]], pos[a]);
            resl = combine(up,resl);
            a = parents[0][head[a]];
        }
        if(a != LCA) {
            lca_taken = true;
            S up = segtree.query(1,1,n,pos[LCA], pos[a]);
            resl = combine(up,resl);
        }
        while(head[b] != head[LCA]){
            S up = segtree.query(1,1,n,pos[head[b]], pos[b]);
            resr = combine(up,resr);
            b = parents[0][head[b]];
        }
        if(b != LCA) {
            lca_taken = true;
            S up = segtree.query(1,1,n,pos[LCA], pos[b]);
            resr = combine(up,resr);
        }
        if(!lca_taken){
            S up = S(arr[LCA]);
            resl = combine(up,resl);
        }
        swap(resl.oz,resl.zo);
        return combine(resl,resr);
    }

    void editVal(int idx, int value)
    {
        segtree.update(1,1,n,pos[idx], value);
        arr[idx] = value;
    }
};

void solve()
{
    int n;
    cin >> n;
    head.resize(n+1);
    HLD hld(n);
    for (int i = 1; i <= n; i++)
        cin >> hld.arr[i];
    for (int i = 2; i <= n; i++) {
        int p;
        cin >> p;
        hld.add_edge(p, i);
    }
    hld.go();
    int q;
    cin >> q;
    while (q--) {
        int qtype;
        cin>>qtype;
        if (qtype == 1) {
            int index, val;
            cin >> index >> val;
            hld.editVal(index, val);
        } else {
            int u, v;
            cin >> u >> v;
            auto res = hld.path_ans(u, v);
            cout << max({ res.oo, res.oz, res.zo, res.zz }) << '\n';
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}