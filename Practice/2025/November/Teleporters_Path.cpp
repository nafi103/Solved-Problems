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
vector<int> in, out, path;
vector<vector<int>> g;

void eulerian_path(int node)
{
    while (out[node] > 0)
    {
        out[node]--;
        eulerian_path(g[node][out[node]]);
    }
    path.push_back(node);
}

void solve()
{
    int n, m;
    cin >> n >> m;
    g.resize(n + 1);
    in.assign(n + 1, 0);
    out.assign(n + 1, 0);
    for (int i = 1; i <= m; i++)
    {
        int u, v;
        cin >> u >> v;
        g[u].push_back(v);
        out[u]++;
        in[v]++;
    }
    bool flag = true;
    for (int i = 2; i < n; i++)
    {
        if (in[i] != out[i])
            flag = false;
    }
    if (!flag or (out[1] - in[1] != 1) or (in[n] - out[n]) != 1)
        cout << "IMPOSSIBLE" << endl;
    else
    {
        eulerian_path(1);
        if(sz(path)!=m+1){
            cout << "IMPOSSIBLE" << endl;
            return;
        }
        reverse(all(path));
        for (auto &node : path)
        {
            cout << node << " ";
        }
        cout << endl;
    }
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