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
 const int N = 3e5;
int a[N], b[N], dp[N][3], n;
 int f(int i, int k){
 if(i >= n)
  return 0;
 int &ans = dp[i][k], j = i + 1 - k;
 if(ans != -1)
  return ans;
 ans = -inf;
 if(i + 3 <= n and j + 3 <= n){
  ans = (a[i] + a[i + 1] + a[i + 2] > 1) + (b[j] + b[j + 1] + b[j + 2] > 1) + f(i + 3, k);
 }
 if(i < j){
  ans = max(ans, (a[i] + a[i + 1] + b[j] > 1) + f(i + 2, 1));
 }
 if(i > j){
  ans = max(ans, (a[i] + b[j] + b[j + 1] > 1) + f(i + 1, 1));
 }
 if(i == j){
  ans = max(ans, (a[i] + b[j] + b[j + 1] > 1) + f(i + 1, 0));
  ans = max(ans, (a[i] + a[i + 1] + b[j] > 1) + f(i + 2, 2));
 }
 return ans;
}
 void solve()
{
 char x;
    cin >> n;
    for(int i = 0; i < n; i++){
     cin >> x;
     a[i] = (x == 'A');
    }
    for(int i = 0; i < n; i++){
     cin >> x;
     b[i] = (x == 'A');
     dp[i][0] = dp[i][1] = dp[i][2] = -1;
    }
    cout << f(0, 1) << endl;
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