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
 map<string, array<int,3>> _hash;
string s;
int dp[1000][1000];
 bool f(int i, int j){
 if(i > j)
  return true;
 int &ans = dp[i][j];
 if(dp[i][j] != -1)
  return dp[i][j];
 if(j - i + 1 <= 3){
  return ans = _hash.count(s.substr(i, j - i + 1));
 }
 ans = false;
 if(_hash.count(s.substr(i, 2))){
  ans |= f(i + 2, j);
 }
 if(_hash.count(s.substr(i, 3))){
  ans |= f(i + 3, j);
 }
 return ans;
}
 void solve()
{
 _hash.clear();
    int n, m;
    cin >> n >> m;
    string str;
    for(int i = 0; i < m; i++){
     for(int j = 0; j < m; j++)
      dp[i][j] = -1;
    }
    for(int i = 0; i < n; i++){
     cin >> str;
     for(int j = 1; j < m; j++){
      int l = j - 1;
      _hash[str.substr(l, 2)] = {l + 1, j + 1, i + 1};
      if(j > 1){
       l = j - 2;
       _hash[str.substr(l, 3)] = {l + 1, j + 1, i + 1};
      }
     }
    }
    cin >> s;
    if(f(0, m - 1) != 1){
     cout << -1 << endl;
     return;
    }
    vector<array<int, 3>> path;
    int i = 0;
    while(i < m){
     if(f(i, i + 1) == 1 and f(i + 2, m - 1) == 1){
      path.push_back(_hash[s.substr(i, 2)]);
      i += 2;
     }else{
      path.push_back(_hash[s.substr(i, 3)]);
      i += 3;
     }
    }
    cout << sz(path) << endl;
    for(auto &[l, r, id]: path){
     cout << l << " " << r << " " <<  id << endl;
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}