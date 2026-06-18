#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
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
const int N = 5e5 + 10;
int dp[N];
 void solve()
{
    int n, c, cnt = 0, mx_sub = 0;
    cin >> n >> c;
     for(int i = 0, x; i < n; i++){
        cin >> x;
         if(x == c)
            cnt++;
        else
            dp[x] = max(dp[x], cnt) + 1;
         mx_sub = max(mx_sub, dp[x] - cnt);
    }
     cout << mx_sub + cnt << endl;
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