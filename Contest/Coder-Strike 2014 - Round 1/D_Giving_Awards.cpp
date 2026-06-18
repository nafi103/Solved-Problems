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
 /*
 * Strongly Connected Components (Kosaraju's Algorithm)
 * Time: O(V + E)
 * Use: Finding SCCs, generating Condensation Graph (DAG)
 */
vector<bool> visited;
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
  void solve()
{
    int n, m;
    cin >> n >> m;
    vector<vector<int>> g(n);
    for(int i = 0, u, v; i < m; i++){
        cin >> u >> v;
        u--, v--;
        g[v].push_back(u);
    }
     vector<vector<int>> components, g_cond;
    vector<int> roots;
    strongly_connected_components(g, components, g_cond, roots);
     m = sz(g_cond);
    vector<int> in_degree(m, 0);
    for(int i = 0; i < m; i++){
        for(auto &adj: g_cond[i])
            in_degree[adj]++;
    }
     queue<int> q;
    for(int i = 0; i < m; i++){
        if(in_degree[i] == 0)
            q.push(i);
    }
     vector<int> topo;
    while(!q.empty()){
        int node = q.front();
        q.pop();
        topo.push_back(node);
         for(auto &adj: g_cond[node]){
            in_degree[adj]--;
            if(in_degree[adj] == 0)
                q.push(adj);
        }
    }
     for(auto &x: topo){
        for(auto &node: components[x]){
            cout << node + 1 << " ";
        }
    }
     cout << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}