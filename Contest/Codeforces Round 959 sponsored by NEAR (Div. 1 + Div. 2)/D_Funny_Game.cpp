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
 void solve()
{
    int n;
    cin >> n;
    vector<int> v(n);
    for(auto &x: v)
     cin >> x;
    set<int> pos;
    for(int i = 0; i < n; i++)
     pos.insert(i);
    vector<pair<int,int>> ans;
    for(int i = n - 1; i > 0; i--){
     vector<int> seen(i, -1);
     for(auto &j: pos){
      if(seen[v[j] % i] != -1){
       ans.emplace_back(j, seen[v[j] % i]);
       pos.erase(j);
       break;
      }
      seen[v[j] % i] = j;
     }
    }
    reverse(ans.begin(), ans.end());
    cout << "YES" << endl;
    for(auto &[a,b]: ans)
     cout << a + 1 << " " << b + 1 << endl;
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