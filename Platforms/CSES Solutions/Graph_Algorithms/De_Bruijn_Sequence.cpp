#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
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
int mod;
vector<array<int,2>> g;
vector<bool> visited;
vector<int> out_degree, ans;

void make_graph(int node){
    visited[node] = true;
    g[node][0] = (node << 1) % mod;
    g[node][1] = ((node << 1) | 1) % mod;
    for(auto &nbr: g[node])
        if(!visited[nbr])
            make_graph(nbr);
}

void euler_path(int node, int in_edge){
    while(out_degree[node]>0){
        out_degree[node]--;
        euler_path(g[node][out_degree[node]], out_degree[node]);
    }
    ans.push_back(in_edge);
}

void solve()
{
    int n;
    cin >> n;
    n--;
    mod = 1 << n;
    g.resize(mod);
    out_degree.assign(mod, 2);
    visited.assign(mod, false);
    make_graph(0);
    euler_path(0,3);
    ans.pop_back();
    reverse(all(ans));
    for (int i = 1; i<=n; i++)
        cout << 0;
    for (auto &x: ans)
        cout << x;
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