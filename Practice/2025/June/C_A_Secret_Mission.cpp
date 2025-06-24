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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

vector<vector<int>>parents;
vector<vector<pair<int,int>>>t;
vector<int>level,value,subtree_size, heavy_child, head, id,st,_parent, _size;
int mx;

void build(int &n) {
    for (int i = n - 1; i > 0; --i) st[i] = max(st[i<<1] , st[i<<1|1]);
}

int query(int l, int r, int &n) {
    int res = INT_MIN;
    for (l += n, r += n; l < r; l >>= 1, r >>= 1) {
        if (l&1) res = max(res, st[l++]);
        if (r&1) res = max(res, st[--r]);
    }
    return res;
}

int dfs(int node, int parent, int cLevel){
    int max_weight = 0;
    level[node] = cLevel;
    parents[0][node] = parent;
    for(auto &[child,weight]: t[node]){
        if(child!=parent){
            dfs(child,node, cLevel+1);
            subtree_size[node]+=subtree_size[child];
            if(subtree_size[child]>max_weight){
                max_weight = subtree_size[child];
                heavy_child[node] = child;
            }
        }
    }
    return subtree_size[node];
}

void dfs_complete(int node, int parent, int weight, int &curr_id,int &n){
    id[node] = curr_id++;
    st[curr_id+n-1] = weight;
    if(head[node]==-1){
        head[node] = node;
    }
    if(heavy_child[node]!=-1){
        int weight = 0;
        for(auto &[child,wt]: t[node]){
            if(child==heavy_child[node]){
                weight = wt;
                break;
            }
        }
        head[heavy_child[node]] = head[node];
        dfs_complete(heavy_child[node],node,weight, curr_id,n);
    }
    for(auto &[child,weight]: t[node]){
        if(child!=parent and child!=heavy_child[node]) dfs_complete(child, node,weight, curr_id,n);
    }
}

int kthParent(int a, int k){
    for(int i = 0; i<mx; i++){
        if(a==-1) return a;
        if(k&(1<<i)) a = parents[i][a];
    }
    return a;
}

int lca(int a, int b){
    if(level[a]>level[b]){
        a = kthParent(a, level[a] - level[b]);
    }else{
        b = kthParent(b, level[b] - level[a]);
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

int path_ans(int a, int b, int &n){
    int LCA = lca(a,b),ans = 0;
    while(head[a] != head[LCA]){
        ans = max(ans, query(id[head[a]], id[a]+1, n));
        a = parents[0][head[a]];
    }
    if(a != LCA) {
        ans = max(ans, query(id[LCA]+1, id[a]+1, n));
    }
    while(head[b] != head[LCA]){
        ans = max(ans, query(id[head[b]], id[b]+1, n));
        b = parents[0][head[b]];
    }
    if(b != LCA) {
        ans = max(ans, query(id[LCA]+1, id[b]+1, n));
    }
    return ans;
}

void initialize(int n){
    _parent.resize(n+1);
    _size.assign(n+1,1); 
    t.resize(n+1);
    parents.assign(mx,vector<int>(n+1,-1));
    subtree_size.resize(n+1,1);
    id.resize(n+1);
    heavy_child.assign(n+1,-1);
    head.assign(n+1,-1);
    st.resize(2*n);
    level.resize(n+1);
    value.resize(n+1);
}

void clear_all(){
    _parent.clear();
    _size.clear(); 
    t.clear();
    parents.clear();
    subtree_size.clear();
    id.clear();
    heavy_child.clear();
    head.clear();
    st.clear();
    level.clear();
    value.clear();
}

int find(int i){ 
    if(_parent[i]==i) return i; 
    return _parent[i] = find(_parent[i]); 
} 

int size(int a){ 
    a = find(a); 
    return _size[a]; 
} 

void Union(int a, int b, int w){ 
    a = find(a); 
    b = find(b); 
    if(a==b) return;
    t[a].push_back({b,w});
    t[b].push_back({a,w});
    if(_size[a]<_size[b]) swap(a,b);
    _parent[b] = a;
    _size[a]+=_size[b]; 
}

void solve()
{
    int n,m;
    cin>>n>>m;
    mx = log2(n) + 2;
    initialize(n);
    for(int i = 1; i<=n; i++) 
        _parent[i] = i; 
    vector<array<int,3>>edges;
    while(m--){
        int u,v,w;
        cin>>u>>v>>w;
        edges.push_back({w,u,v});
    }
    sort(all(edges));
    for(auto &[w,u,v]: edges){
        Union(u,v,w);
    }
    dfs(1,-1,0);
    int curr_id = 0;
    dfs_complete(1,-1,0,curr_id,n);
    build(n);
    for(int i = 1; i<mx; i++){
        for(int j = 1; j<=n; j++){
            int prevParent = parents[i-1][j];
            if(prevParent!=-1)  parents[i][j] = parents[i-1][prevParent];
        }
    }
    int q;
    cin>>q;
    while(q--){
        int a,b;
        cin>>a>>b;
        cout<<path_ans(a,b,n)<<endl;
    }
    clear_all();
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<":\n";
        solve();
    }
}