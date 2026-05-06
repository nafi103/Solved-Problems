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
    vector<vector<int>> grid(n, vector<int>(m, 0ll)), dp(n, vector<int>(m, -inf));
    for(int i = 0; i < n; i++){
        for(int j = 0; j < m; j++){
            cin >> grid[i][j];
            if(i == 0 and j == 0)
                dp[i][j] = grid[i][j];
            if(i)
                dp[i][j] = max(dp[i][j], dp[i - 1][j] + grid[i][j]);
            if(j)
                dp[i][j] = max(dp[i][j], dp[i][j - 1] + grid[i][j]);
        }
    }
    auto valid = [&](int x, int y){
        return x >= 0 and y >= 0 and x < n and y < m;
    };
    int r = n - 1, c = m - 1, mx = grid[r][c], tr = r, tc = c;
    while(r or c){
        int lr = r, lc = c - 1;
        int ur = r - 1, uc = c, nr, nc;
        if(valid(lr, lc)){
            if(dp[lr][lc] + grid[r][c] == dp[r][c]){
                nr = lr;
                nc = lc;
            }
        }
        if(valid(ur, uc)){
            if(dp[ur][uc] + grid[r][c] == dp[r][c]){
                nr = ur;
                nc = uc;
            }
        }
        r = nr, c = nc;
        if(grid[r][c] > grid[tr][tc]){
            tr = r;
            tc = c;
        }
    }
    if(grid[tr][tc] <= 0){
        cout << dp[n - 1][m - 1] << endl;
        return;
    }
    grid[tr][tc] = -grid[tr][tc];
    for(int i = 0; i < n; i++){
        for(int j = 0; j < m; j++){
            if(i == 0 and j == 0){
                dp[i][j] = grid[i][j];
                continue;
            }
            dp[i][j] = -inf;
            if(i)
                dp[i][j] = max(dp[i][j], dp[i - 1][j] + grid[i][j]);
            if(j)
                dp[i][j] = max(dp[i][j], dp[i][j - 1] + grid[i][j]);
        }
    }
    cout << dp[n - 1][m - 1] << endl;
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