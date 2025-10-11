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
#define all(x) x.begin(), x.end()
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

vector<bool>visited;

void dfs(int v, vector<vector<int>> const& g, vector<int>& output) {
    visited[v] = true;
    for (auto u : g[v])
        if (!visited[u])
            dfs(u, g, output);
    output.push_back(v);
}

void strongly_connected_components(vector<vector<int>> const& g,
                                vector<vector<int>>& components,
                                vector<vector<int>>& g_cond,
                                vector<int>& roots) {
    int n = sz(g);
    components.clear(); g_cond.clear();

    vector<int> order;
    visited.assign(n, false);

    for (int i = 0; i < n; ++i)
        if (!visited[i])
            dfs(i, g, order);

    vector<vector<int>> g_rev(n);
    for (int v = 0; v < n; ++v)
        for (int u : g[v])
            g_rev[u].push_back(v);

    visited.assign(n, false);
    reverse(order.begin(), order.end());

    roots.assign(n, -1);
    int component_id = 0;

    for (int v : order) {
        if (!visited[v]) {
            vector<int> component;
            dfs(v, g_rev, component);
            for (int u : component)
                roots[u] = component_id;
            components.push_back(component);
            component_id++;
        }
    }

    g_cond.assign(component_id, {});
    for (int v = 0; v < n; ++v) {
        for (int u : g[v]) {
            if (roots[v] != roots[u]) {
                g_cond[roots[v]].push_back(roots[u]);
            }
        }
    }
}
vector<vector<int>>components,g_cond,max_path;
vector<int>w;
int k;

void dfs(int node){
    max_path[node][1] = w[node];
    visited[node] = true;
    for(auto &x: g_cond[node]){
        if(!visited[x])
            dfs(x);
    }
    for(int i = 1; i<=k; i++){
        for(auto &child: g_cond[node]){
            max_path[node][i] = max(max_path[node][i],max_path[child][i-1]+w[node]);
        }
    }
}


void solve()
{
    w.clear();
    max_path.clear();
    int n,m,u,v;
    cin>>n>>m>>k;
    vector<vector<int>>g(n);
    vector<int>roots;
    for(int i = 0; i<m; i++){
        cin>>u>>v;
        u--,v--;
        g[u].push_back(v);
    }
    strongly_connected_components(g,components,g_cond,roots);
    w.assign(g_cond.size(),0);
    for(auto &x: roots){
        w[x]++;
    }
    int nn = g_cond.size();
    max_path.assign(nn,vector<int>(k+1,0));
    visited.assign(nn,false);
    for(int i = 0; i<nn; i++){
        if(!visited[i])
            dfs(i);
    }
    int ans = 0;
    for(int i = 0; i<nn; i++){
        for(int j = 1; j<=k; j++){
            ans = max(ans,max_path[i][j]);
        }
    }
    cout<<ans<<endl;
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}