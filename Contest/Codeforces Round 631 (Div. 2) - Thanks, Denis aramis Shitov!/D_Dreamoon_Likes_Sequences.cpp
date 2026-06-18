#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int N = 31;
int d, m, r;
int dp[N][N][N];
// I have length i, I will use bit k at position j
 int f(int len, int pos, int msb){
 if(pos == len){
  if(msb > r)
   return 0ll;
  int ub = min(d, (1ll << (msb + 1)) - 1);
  int lb = (1ll << msb) - 1;
  return max(0ll, ub - lb);
 }
 if(msb > r)
  return 0ll;
 int &ans = dp[len][pos][msb];
 if(ans != -1)
  return ans;
 ans = 0;
 int ub = min(d, (1ll << (msb + 1)) - 1);
 int lb = (1ll << msb) - 1;
 int available = max(0ll, ub - lb);
 for(int nextMsb = msb + 1; nextMsb < N; nextMsb++){
  ans = (ans + available * f(len, pos + 1, nextMsb)) % m;
 }
 return ans;
}
 void solve()
{
 memset(dp, -1, sizeof dp);
    cin >> d >> m;
    r = 63ll - __builtin_clzll(d);
    debug(r)
    int ans = 0;
    for(int len = 1; len < N; len++){
     for(int b = 0; b < N; b++){
      ans = (ans + max(0ll, f(len, 1, b))) % m;
     }
    }
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
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}