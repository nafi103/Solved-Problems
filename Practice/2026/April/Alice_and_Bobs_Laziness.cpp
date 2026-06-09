#pragma GCC optimize("Ofast")
#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

struct Node
{
    int a, b;

    Node(){
        a = 0, b = 0;
    }

    Node(int val){
        a = 0, b = 0;
        if(val >= 64){
            val -= 64;
            b = (1ll << val);
        }else{
            a = (1ll << val);
        }
    }
};

Node merge(Node l, Node r){
    Node res;
    res.a |= l.a;
    res.a |= r.a;
    res.b |= l.b;
    res.b |= r.b;
    return res;
}

struct Segment_Tree
{
    int n;
    vector<Node> st;
    vector<int> v;

    Segment_Tree(int _n)
    {
        n = _n;
        st.resize(4 * n);
    }

    Segment_Tree(vector<int> &_v, int _n){
        n = _n;
        st.resize(4 * n);
        v = _v;
        build(1, 1, n);
    }

    void build(int node, int b, int e)
    {
        if (b == e)
        {
            st[node] = Node(v[b]);
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        build(left, b, mid);
        build(right, mid + 1, e);
        st[node] = merge(st[left], st[right]);
    }

    void update(int node, int b, int e, int &idx, Node &value)
    {
        if (e < idx or b > idx)
            return;
        if (b == idx and e == idx)
        {
            st[node] = value;
            return;
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        update(left, b, mid, idx, value);
        update(right, mid + 1, e, idx, value);
        st[node] = merge(st[left], st[right]);
    }

    Node query(int node, int b, int e, int &l, int &r)
    {
        if (e < l or b > r)
            return Node();
        if (b >= l and e <= r)
        {
            return st[node];
        }
        int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
        Node query_left = query(left, b, mid, l, r), query_right = query(right, mid + 1, e, l, r);
        return merge(query_left, query_right);
    }

    void update(int i, int val){
        Node tmp(val);
        update(1, 1, n, i, tmp);
    }

    Node query(int l, int r){
        return query(1, 1, n, l, r);
    }
};

struct HLD {
    int n, cur_pos = 1;
    vector<int> arr, parent, size, depth, heavy, head, pos;
    vector<vector<int>> adj;
    Segment_Tree segtree;
    HLD(int n)  : n(n), arr(n + 1), parent(n + 1), size(n + 1), depth(n + 1), heavy(n + 1, 0), head(n + 1) , pos(n + 1) , adj(n + 1), segtree(Segment_Tree(n)){ }
    void add_edge(int u, int v)  {
        adj[u].push_back(v), adj[v].push_back(u);
    }
    void dfs(int u, int p) {
        parent[u] = p;
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
    void decompose(int u, int h) {
        head[u] = h;
        pos[u] = cur_pos++;
        segtree.update(pos[u], arr[u]);
        if (heavy[u])
            decompose(heavy[u], h);
        for (int v : adj[u])
            if (v != parent[u] && v != heavy[u])
                decompose(v, v);
    }
    Node query(int u, int v) {
        Node res;
        while (head[u] != head[v]) {
            if (depth[head[u]] < depth[head[v]])
                swap(u, v);
            res = merge(res, segtree.query(pos[head[u]], pos[u]));
            u = parent[head[u]];
        }
        if (depth[u] > depth[v])
            swap(u, v);
        res = merge(res, segtree.query(pos[u], pos[v]));
        return res;
    }
    int distance(int u, int v) {
        int res = 0;
        while (head[u] != head[v]) {
            if (depth[head[u]] < depth[head[v]])
                swap(u, v);
            res += pos[u] - pos[head[u]] + 1;
            u = parent[head[u]];
        }
        if (depth[u] > depth[v])
            swap(u, v);
        res += pos[v] - pos[u] + 1;
        return res;
    }
    void editVal(int idx, int value) {
        segtree.update(pos[idx], value);
        arr[idx] = value;
    }
};

unordered_map<int,int> compress;

const int N = 1e6 + 10;
int sigma[N];


void solve()
{
    int n, q;
    cin >> n >> q;
    vector<int> arr(n + 1);
    for(int i = 1; i <= n; i++){
        cin >> arr[i];
        arr[i] = compress[sigma[arr[i]]];
    }
    // Segment_Tree st(arr, n);
    // for(int i = 2; i <= n; i++){
    //     map<int,int> res = st.query(1, i).cnt;
    //     debug(res)
    // }
    HLD hld(n);
    for(int i = 1, u, v; i < n; i++){
        cin >> u >> v;
        hld.add_edge(u, v);
    }
    hld.dfs(1, 0);
    hld.decompose(1, 1);
    for(int node = 1; node <= n; node++){
        hld.editVal(node, arr[node]);
    }
    while(q--){
        char type;
        cin >> type;
        if(type == 'A'){
            int node, val;
            cin >> node >> val;
            hld.editVal(node, compress[sigma[val]]);
        }else{
            int u, v;
            cin >> u >> v;
            Node res = hld.query(u, v);
            int same = __builtin_popcountll(res.a) + __builtin_popcountll(res.b);
            cout << hld.distance(u, v) - same << endl;
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    for(int i = 1; i <= N; i++){
        for(int j = i; j <= N; j += i)
            sigma[j]++;
    }
    map<int,int> cnt;
    for(int i = 1; i <= N; i++){
        cnt[sigma[i]]++;
    }
    for(auto &[f, s]: cnt){
        compress[f] = sz(compress);
    }
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}