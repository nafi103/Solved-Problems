#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int N = 1e5 + 10;
int dp[N], c[50], h[50], pref[50];
 void solve()
{
    int n,x;
    cin >> n >> x;
    for(int i = 0; i < n; i++){
     cin >> c[i] >> h[i];
     pref[i] = h[i];
     if(i)
      pref[i] += pref[i - 1];
    }
    for(int i = pref[n - 1]; i > 0; i--){
     dp[i] = inf;
    }
    for(int i = 0, curr = 0; i < n; i++, curr += x){
     for(int j = pref[i]; j >= h[i]; j--){
      if(dp[j - h[i]] + c[i] <= curr)
       dp[j] = min(dp[j], dp[j - h[i]] + c[i]);
     }
    }
    for(int i = pref[n - 1]; i >= 0; i--){
     if(dp[i] != inf){
      cout << i << endl;
      break;
     }
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
    cin >> t;
    dp[0] = 0;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}