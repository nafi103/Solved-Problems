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

    vector<int> arr(n), dp(n + 1, 0);
    for(int i = 0; i < n; i++)
        cin >> arr[i];

    for(int i = n - 1; i >= 0; i--){
        for(int j = i, mx = arr[i]; j < min(n, i + k); j++){
            mx = max(mx, arr[j]);
            dp[i] = max(dp[i], (j - i + 1) * mx + dp[j + 1]);
        }
    }

    cout << dp[0] << endl;
}

int32_t main()
{
    freopen("teamwork.in", "r", stdin);
    freopen("teamwork.out", "w", stdout);
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