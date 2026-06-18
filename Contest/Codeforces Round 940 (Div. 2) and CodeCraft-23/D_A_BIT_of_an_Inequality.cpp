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
 const int M = 31;
 void add(vector<int> &cnt, int &x){
 for(int j = 0; j < M; j++){
  if(x & (1 << j))
   cnt[j]++;
 }
}
 void sub(vector<int> &cnt, int &x){
 for(int j = 0; j < M; j++){
  if(x & (1 << j))
   cnt[j]--;
 }
}
 void solve()
{
    int n, ans = 0;
    cin >> n;
    vector<int> v(n + 1, 0), pref(M, 0), suff(M, 0), msb(n + 1, 0);
    for(int i = 1; i <= n; i++){
     cin >> v[i];
     msb[i] = 63 - __builtin_clzll(v[i]);
     v[i] = v[i] ^ v[i - 1];
     add(suff, v[i]);
    }
    for(int i = 1; i<=n; i++){
     int left1 = pref[msb[i]], right1 = suff[msb[i]], left0 = i - left1, right0 = n - i + 1 - right1;
     ans += (left1 * right1) + (left0 * right0);
     add(pref, v[i]);
     sub(suff, v[i]);
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