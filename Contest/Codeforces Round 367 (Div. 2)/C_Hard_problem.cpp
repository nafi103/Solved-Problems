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
    vector<int> cost(n);
    for(auto &x: cost)
        cin >> x;
     vector<vector<string>> str(n, vector<string>(2));
    for(int i = 0; i < n; i++){
        cin >> str[i][0];
        str[i][1] = str[i][0];
        reverse(all(str[i][1]));
    }
     vector<vector<int>> dp(n, vector<int>(2, inf));
    dp[0][0] = 0; dp[0][1] = cost[0];
    for(int i = 1; i < n; i++){
        for(int j = 0; j < 2; j++){
            for(int k = 0; k < 2; k++){
                if(str[i][j] >= str[i - 1][k]){
                    dp[i][j] = min(dp[i][j], dp[i - 1][k] + cost[i] * j);
                }
            }
        }
    }
     int ans = min(dp[n - 1][0], dp[n - 1][1]);
     cout << (ans != inf ? ans : -1) << endl;
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