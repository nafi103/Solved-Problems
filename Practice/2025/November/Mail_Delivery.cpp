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

vector<int> euler_circuit;

void find_euler_circuit(int node, vector<multiset<int>> &g)
{
    while (!g[node].empty())
    {
        int nbr = *g[node].begin();
        g[nbr].erase(g[nbr].find(node));
        g[node].erase(g[node].begin());
        find_euler_circuit(nbr, g);
    }
    euler_circuit.push_back(node);
}

void solve()
{
    int n, m;
    cin >> n >> m;
    vector<multiset<int>> g(n + 1);
    vector<int> degree(n + 1, 0);
    for (int i = 1; i <= m; i++)
    {
        int u, v;
        cin >> u >> v;
        if (u > v)
            swap(u, v);
        g[u].insert(v);
        g[v].insert(u);
        degree[u]++;
        degree[v]++;
    }

    int odd_degree = 0;
    for (int i = 1; i <= n; i++)
    {
        if (degree[i] & 1)
            odd_degree++;
    }

    find_euler_circuit(1, g);

    if (odd_degree == 0 and sz(euler_circuit)==m+1)
    {
        for (auto &node : euler_circuit)
            cout << node << " ";
        cout << endl;
    }
    else
    {
        cout << "IMPOSSIBLE" << endl;
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