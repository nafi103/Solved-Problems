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
    int n,x, ans = 0;
    cin >> n >> x;
    vector<int> v(n);
    for(auto &y: v)
     cin >> y;
    set<int> s = {1};
    for(auto &y: v){
     if(y == 1 or x % y != 0)
      continue;
     vector<int> add;
     for(auto &z: s){
      if(z * y > x)
       break;
      if(x % (z * y) == 0)
       add.push_back(z * y);
     }
     for(auto &z: add)
      s.insert(z);
     if(s.count(x)){
      ans++;
      s = {1, y};
     }
    }
    if(sz(s) > 1 or ans == 0)
     ans++;
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