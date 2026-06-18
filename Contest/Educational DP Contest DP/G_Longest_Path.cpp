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

    int in_degree[n];
    memset(in_degree, 0, sizeof in_degree);

    vector<vector<int>> g(n);
    for(int i = 0, u, v; i < m; i++){
        cin >> u >> v;
        u--, v--;
        g[u].push_back(v);
        in_degree[v]++;
    }

    vector<int> dp(n, 0);
    queue<int> q;
    for(int i = 0; i < n; i++){
        if(in_degree[i] == 0)
            q.push(i);
    }

    int ans = 0;
    while(!q.empty()){
        int node = q.front();
        q.pop();
        ans = max(ans, dp[node]);

        for(auto &adj: g[node]){
            in_degree[adj]--;
            dp[adj] = max(dp[adj], dp[node] + 1);
            if(in_degree[adj] == 0)
                q.push(adj);
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
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}