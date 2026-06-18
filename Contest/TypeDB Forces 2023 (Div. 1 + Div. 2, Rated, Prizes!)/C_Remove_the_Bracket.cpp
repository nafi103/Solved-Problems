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
    int n, s;
    cin >> n >> s;
    vector<int> x(n), y(n);
    for(int i = 0, val; i < n; i++){
        cin >> val;
        if(i == 0 or i == n - 1)
            x[i] = y[i] = val;
        else if(val <= s){
            x[i] = 0; y[i] = val;
        }else{
            x[i] = s; y[i] = val - s;
        }
    }
     vector<vector<int>> dp(n, vector<int> (2, 0));
    for(int i = 1; i < n; i++){
        dp[i][0] = min(dp[i - 1][0] + y[i - 1] * x[i], dp[i - 1][1] + x[i - 1] * x[i]);
        dp[i][1] = min(dp[i - 1][0] + y[i - 1] * y[i], dp[i - 1][1] + x[i - 1] * y[i]);
    }
    cout << dp[n - 1][0] << endl;
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