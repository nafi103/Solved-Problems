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

void solve()
{
    int n, m;
    cin >> n >> m;
    vector<vector<int>> g(n + 1);
    while(m--){
        int u, v;
        cin >> u >> v;
        g[u].push_back(v);
    }
    queue<int> q;
    q.push(1);
    int ans = 1;
    vector<bool> visited(n + 1, false);
    visited[1] = true;
    while(!q.empty()){
        int node = q.front();
        q.pop();
        for(auto &adj: g[node]){
            if(!visited[adj]){
                visited[adj] = true;
                ans++;
                q.push(adj);
            }
        }
    }
    cout << ans << endl;
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