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
    vector<int> ans(n + 1, 0);
    vector<vector<int>> dp(2, vector<int>(n + 1, 0));
    dp[0][0] = 1;
    int zero = k;
    while(zero <= n){
        for(int j = zero; j <= n; j++){
            dp[1][j] = 0;
            dp[1][j] += dp[0][j - k];
            if(j - k >= zero)
                dp[1][j] += dp[1][j - k];
            dp[1][j] %= mod;
            ans[j] = (ans[j] + dp[1][j]) % mod;
        }
        k++;
        zero += k;
        swap(dp[0], dp[1]);
    }
    for(int i = 1; i <= n; i++){
        cout << ans[i] << " \n"[i == n];
    }
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