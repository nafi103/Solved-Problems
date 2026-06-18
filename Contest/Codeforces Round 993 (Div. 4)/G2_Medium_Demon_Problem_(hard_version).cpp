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
    int n;
    cin >> n;
    vector<vector<int>> g(n), components, g_cond;
    vector<int> roots;
    for(int u = 0, v; u < n; u++){
        cin >> v;
        v--;
        g[u].push_back(v);
    }
     strongly_connected_components(g, components, g_cond, roots);
     n = sz(g_cond);
     vector<int> dp(n, 1), in_degree(n, 0);
    for(int node = 0; node < n; node++){
        for(auto &adj: g_cond[node]){
            in_degree[adj]++;
        }
    }
     queue<pair<int,int>> q;
    for(int node = 0; node < n; node++){
        if(in_degree[node] == 0){
            q.push({node, 1});
        }
    }
     vector<bool> cycle(n, false);
    while(!q.empty()){
        auto [node, d] = q.front();
        q.pop();
         if(g_cond[node].empty())
            cycle[node] = true;
         for(auto &adj: g_cond[node]){
            in_degree[adj]--;
            dp[adj] += d;
             if(in_degree[adj] == 0){
                q.push({adj, dp[adj]});
            }
        }
    }
     int mx = 0;
    for(int i = 0; i < n; i++){
        if(!cycle[i])
            mx = max(mx, dp[i]);
    }
     cout << mx + 2 << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}