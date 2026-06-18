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

vector<bool> visited;

void dfs(int node, vector<vector<int>>&g, vector<int>&order){
    visited[node] = true;
    for(auto &nbr: g[node]){
        if(!visited[nbr])
            dfs(nbr, g, order);
    }
    order.push_back(node);
}

void strongly_connected_component(
    vector<vector<int>> &g,
    vector<vector<int>> &g_rev,
    vector<vector<int>> &g_cond,
    vector<vector<int>> &components,
    vector<int> &values)
{
    int n = sz(g);

    components.clear();
    g_cond.clear();
    vector<int> order, component;
    
    visited.assign(n, false);
    for (int i = 0; i < n; i++){
        if(!visited[i])
            dfs(i, g, order);
    }

    visited.assign(n, false);
    vector<int> roots(n, 0);
    for (int i = n - 1, root = 0; i >= 0; i--){
        if(!visited[order[i]]){
            dfs(order[i], g_rev, component);
            components.push_back(component);
            for (auto &node: component){
                roots[node] = root;
            }
            component.clear();
            root++;
        }
    }

    vector<int> tmp_value(sz(components), 0);
    for (int i = 0; i < sz(components); i++){
        for (auto &node: components[i])
            tmp_value[i] += values[node];
    }
    values = tmp_value;

    g_cond.assign(sz(components), {});
    for (int v = 0; v < n; v++)
        for (auto u : g[v])
            if (roots[v] != roots[u])
                g_cond[roots[v]].push_back(roots[u]);
}

void solve()
{
    int n, m;
    cin >> n >> m;
    vector<int> values(n), now_value;
    vector<vector<int>> g(n), g_cond, g_rev(n), components;
    for(auto &x: values)
        cin >> x;
    for (int i = 0; i < m; i++){
        int u , v;
        cin >> u >> v;
        u--, v--;
        g[u].push_back(v);
        g_rev[v].push_back(u);
    }

    strongly_connected_component(g, g_rev, g_cond, components, values);
    
    n = sz(g_cond);
    vector<int> in_degree(n, 0);
    for (int i = 0; i < n; i++){
        for(auto &nbr: g_cond[i])
            in_degree[nbr]++;
    }

    vector<int> path_value(n, 0);
    priority_queue<pair<int,int>> pq;
    for (int i = 0; i < n; i++){
        if(in_degree[i] == 0){
            path_value[i] = values[i];
            pq.push({values[i], i});
        }
    }

    while(!pq.empty()){
        auto [value, node] = pq.top();
        pq.pop();
        if(path_value[node]>value)
            continue;
        for(auto &nbr: g_cond[node]){
            if(path_value[nbr] < value + values[nbr]){
                path_value[nbr] = value + values[nbr];
                pq.push({path_value[nbr], nbr});
            }
        }
    }

    cout << *max_element(all(path_value)) << endl;
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