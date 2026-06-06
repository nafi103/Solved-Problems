#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

// #ifndef ONLINE_JUDGE
// #include "debug.h"
// #define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
// #else
// #define debug(...)
// #endif

/****************************************************************/

void solve()
{
    int n, k;
    cin >> n >> k;
    vector<int> arr(n);
    for(int i = 0; i < n; i++)
        cin >> arr[i];

    int dp[n + 1][k + 1];
    for(int j = 0; j <= k; j++)
        dp[n][j] = 0;

    for(int i = 0; i < n; i++){
        for(int j = 0; j <= k; j++){
            dp[i][j] = inf;
        }
    }

    for(int i = n - 1, suff_mx = arr[i], sum = 0; i >= 0; i--){

        suff_mx = max(suff_mx, arr[i]);
        sum += arr[i];
        dp[i][0] = (n - i) * suff_mx - sum;

        for(int j = 1; j <= k; j++){
            for(int l = i, mx = arr[i], s = 0; l < n; l++){
                mx = max(mx, arr[l]);
                s += arr[l];
                dp[i][j] = min(dp[i][j], (l - i + 1) * mx - s + dp[l + 1][j - 1]);
            }
        }
    }

    cout << dp[0][k] << endl;
}

int32_t main()
{
    freopen("snakes.in", "r", stdin);
    freopen("snakes.out", "w", stdout);
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