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
int k;
 vector<int> get(vector<int> &a , vector<int> &b){
 vector<int> temp(k);
 for(int i = 0; i<k; i++){
  if(a[i] == b[i])
   temp[i] = a[i];
  else
   temp[i] = 3 ^ (a[i] ^ b[i]);
 }
 return temp;
}
 void solve()
{
    int n, ans = 0;
    cin>>n>>k;
    set<vector<int>> present;
    vector<vector<int>> card(n,vector<int> (k));
    for(int i = 0; i < n; i++){
     for(auto &x: card[i])
      cin>>x;
     present.insert(card[i]);
    }
    map<vector<int> , int> cnt;
    for(int i = 0; i<n-1; i++){
     for(int j = i+1; j<n; j++){
      cnt[get(card[i],card[j])]++;
     }
    }
    for(auto &[v, c]: cnt){
     if(present.count(v))
      ans+= (c*(c-1))>>1;
    }
    cout<<ans<<endl;
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