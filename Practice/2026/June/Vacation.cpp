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
    int n;
    cin >> n;
    vector<array<int, 3>> arr(n);
    for(int i = 0; i < n; i++){
        for(auto &x: arr[i])
            cin >> x;
    }

    int dp[2][3];
    for(int i = 0; i < 2; i++){
        for(int j = 0; j < 3; j++){
            dp[i][j] = -inf;
        }
    }

    dp[0][0] = arr[0][0];
    dp[0][1] = arr[0][1];
    dp[0][2] = arr[0][2];

    for(int i = 1; i < n; i++){
        for(int j = 0; j < 3; j++){
            dp[1][j] = -inf;
            for(int jp = 0; jp < 3; jp++){
                if(jp == j)
                    continue;
                dp[1][j] = max(dp[1][j], dp[0][jp] + arr[i][j]);
            }
        }

        swap(dp[0], dp[1]);
    }

    int ans = 0;
    for(int j = 0; j < 3; j++)
        ans = max(ans, dp[0][j]);

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