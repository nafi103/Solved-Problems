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
    int n, m;
    cin >> n >> m;
    vector<int> arr(n + 1), window(m);
    for(int i = 0; i < m; i++)
     cin >> window[i];
    if(accumulate(all(window), 0ll) < n){
     cout << -1 << endl;
     return;
    }
    vector<int> ans(m);
    for(int i = n, j = 0; j < m; i--, j++){
     int l = i - window[j] + 1;
     if(l < 1){
      cout << -1 << endl;
      return;
     }
     ans[j] = l;
    }
    // debug(ans)
    if(ans[m - 1] != 1){
     ans[m - 1] = 1;
    }
    for(int i = m - 2; i >= 0; i--){
     int empty_cell = ans[i + 1] + window[i + 1];
     if(empty_cell < ans[i]){
      ans[i] = empty_cell;
     }
    }
    for(int i = 0; i < m; i++){
     cout << ans[i] << " \n"[i == m - 1];
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