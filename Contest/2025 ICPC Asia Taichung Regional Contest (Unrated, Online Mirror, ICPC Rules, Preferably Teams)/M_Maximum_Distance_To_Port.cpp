#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
vector<bool> visited;
vector<int> goods,dis;
vector<vector<int>> g;

void bfs(int node, int level){
    vector<int> depth(sz(g));
    queue<pair<int, int>>
        p;
    p.push({node, 0});
    visited[node] = true;
    while(!p.empty()){
        auto [f, l] = p.front();
        depth[f] = l;
        dis[goods[f]] = max(dis[goods[f]], l);
        p.pop();
        for(auto &nbr: g[f]){
            if(!visited[nbr]){
                visited[nbr] = true;
                p.push({nbr, l + 1});
            }
        }
    }
}

void solve()
{
    int n, m, k;
    cin >> n >> m >> k;
    g.resize(n + 1);
    visited.assign(n + 1, false);
    goods.resize(n + 1);
    dis.assign(k + 1, -inf);
    for (int i = 1; i <= n; i++){
        cin >> goods[i];
    }
    while(m--){
        int u, v;
        cin >> u >> v;
        g[u].push_back(v);
        g[v].push_back(u);
    }
    bfs(1, 0);
    for (int i = 1; i <= k; i++)
        cout << dis[i] << " ";
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