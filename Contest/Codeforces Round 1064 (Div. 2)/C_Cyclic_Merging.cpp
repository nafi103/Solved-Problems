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
    vector<int> arr(n), left(n), right(n);
    for(int i = 0; i < n; i++){
     cin >> arr[i];
     left[i] = (i - 1 + n) % n;
     right[i] = ( i + 1) % n;
    }
    set<pair<int,int>> s;
    for(int i = 0; i < n; i++){
     if(arr[left[i]] >= arr[i]){
      s.insert({arr[left[i]], i});
     }else{
      s.insert({arr[i], left[i]});
     }
     if(arr[right[i]] > arr[i]){
      s.insert({arr[right[i]], i});
     }else{
      s.insert({arr[i], right[i]});
     }
    }
    int ans = 0;
    for(int i = 0; i < n - 1; i++){
     auto [val, id] = *s.begin();
     ans += val;
     s.erase(s.begin());
     int l = left[id], r = right[id];
     if(s.count({arr[l], id})){
      s.erase({arr[l], id});
     }
     if(s.count({arr[r], id})){
      s.erase({arr[r], id});
     }
     left[r] = l;
     right[l] = r;
     if(arr[l] >= arr[r]){
      s.insert({arr[l], r});
     }else{
      s.insert({arr[r], l});
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