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
    int n, k;
    cin >> n >> k;
    vector<int> hash(k);
    char grid[n][n];
    int dp[n][n], ans[k];
    memset(ans, 0, sizeof ans);
    for(int i = 0; i < n; i++){
        for(int j = 0; j < n; j++){
            cin >> grid[i][j];
            char &c = grid[i][j];
            if(i and j and grid[i - 1][j] == c and grid[i][j - 1] == c){
                int mn = min(dp[i - 1][j], dp[i][j - 1]);
                if(grid[i - mn][j - mn] == c)
                    mn++;
                dp[i][j] = mn;
            }else
                dp[i][j] = 1;

            ans[c - 'A'] += dp[i][j];
        }
    }
    for(int i = 0; i < k; i++)
        cout << ans[i] << endl;
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