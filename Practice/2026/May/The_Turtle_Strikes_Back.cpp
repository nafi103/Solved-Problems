#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18;

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

    vector<vector<vector<int>>> dp(2, vector<vector<int>>(n + 2, vector<int>(m + 2, -inf))), mx = dp;
    vector<vector<int>> grid(n + 1, vector<int>(m + 1));
    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= m; j++){
            cin >> grid[i][j];
            dp[0][i][j] = dp[1][i][j] = grid[i][j];
        }
    }

    dp[0][0][1] = dp[0][1][0] = 0;
    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= m; j++){
            dp[0][i][j] += max(dp[0][i - 1][j], dp[0][i][j - 1]);
        }
    }

    dp[1][n + 1][m] = dp[1][n][m + 1] = 0;
    for(int i = n; i >= 1; i--){
        for(int j = m; j >= 1; j--){
            dp[1][i][j] += max(dp[1][i + 1][j], dp[1][i][j + 1]);
        }
    }

    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= m; j++){
            mx[0][i][j] = mx[1][i][j] = (dp[0][i][j] + dp[1][i][j] - grid[i][j]);
        }
    }

    for(int i = 1; i <= n; i++){
        for(int j = m; j >= 1; j--){
            mx[0][i][j] = max({mx[0][i][j], mx[0][i - 1][j], mx[0][i][j + 1]});
        }
    }
    for(int i = n; i >= 1; i--){
        for(int j = 1; j <= m; j++){
            mx[1][i][j] = max({mx[1][i][j], mx[1][i + 1][j], mx[1][i][j - 1]});
        }
    }

    int ans = inf;
    for(int i = 1; i <= n; i++){
        for(int j = 1; j <= m; j++){
            int go_through = max(dp[0][i - 1][j], dp[0][i][j - 1]) + 
                             max(dp[1][i + 1][j], dp[1][i][j + 1]) + (-grid[i][j]);

            ans = min(ans, max({go_through, mx[0][i - 1][j + 1], mx[1][i + 1][j - 1]} ));
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}