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
    vector<vector<int>> g(n), components, g_cond;
    vector<int> value(n), roots;
    for(auto &x: value)
        cin >> x;

    while(m--){
        int u, v;
        cin >> u >> v;
        u--, v--;
        if(u == v)
            continue;
        g[u].push_back(v);
    }
    for(auto &v: g){
        sort(all(v));
        v.erase(unique(all(v)), v.end());
    }

    strongly_connected_components(g, components, g_cond, roots);
    int nn = sz(g_cond);
    vector<int> value_p(nn, 0), _size(nn, 0);
    for(int i = 0; i < nn; i++){
        for(auto &x: components[i])
            value_p[i] += value[x];
        _size[i] = sz(components[i]);
    }

    vector<int> in_degree(nn, 0);
    for(auto &v: g_cond){
        for(auto &adj: v)
            in_degree[adj]++;
    }

    queue<int> q;
    vector<int> dp(nn, inf), path(nn, 0);
    for(int i = 0; i < nn; i++){
        if(in_degree[i] == 0){
            q.push(i);
            dp[i] = value_p[i];
            path[i] = _size[i];
        }
    }

    while(!q.empty()){
        auto node = q.front();
        q.pop();
        for(auto &adj: g_cond[node]){
            in_degree[adj]--;
            if(path[adj] < path[node] + _size[adj]){
                path[adj] = path[node] + _size[adj];
                dp[adj] = dp[node] + value_p[adj];
            }else if(path[adj] == path[node] + _size[adj]){
                dp[adj] = min(dp[adj], dp[node] + value_p[adj]);
            }
            if(in_degree[adj] == 0){
                q.push(adj);
            }
        }
    }

    int mx_path = -1, path_val = inf;
    for(int i = 0; i < nn; i++){
        if(path[i] > mx_path){
            mx_path = path[i];
            path_val = dp[i];
        }else if(path[i] == mx_path){
            path_val = min(path_val, dp[i]);
        }
    }

    cout << mx_path << " " << path_val << endl;
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