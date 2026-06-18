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
 void cyclic_shift(string &str){
 reverse(all(str));
 reverse(str.begin()+1, str.end());
}
 void solve()
{
    int n;
    cin >> n;
    string str;
    cin >> str;
    vector<int> p(n+1);
    for(int i = 1; i <= n; i++){
     cin >> p[i];
    }
    vector<vector<int>> cycles;
    vector<bool> visited(n+1, false);
    for(int i = 1; i <= n; i++){
     if(!visited[i]){
      vector<int> temp;
      int curr = i;
      while(p[curr] != i){
       visited[curr] = true;
       temp.push_back(curr);
       curr = p[curr];
      }
      visited[curr] = true;
      temp.push_back(curr);
      cycles.push_back(temp);
     }
    }
    vector<string> str_cycle;
    for(auto &v: cycles){
     string tmp = "";
     for(auto &x: v){
      tmp.push_back(str[x-1]);
     }
     str_cycle.push_back(tmp);
    }
    int ans = 1;
    for(auto &s: str_cycle){
     string tmp = s;
     int cnt = 1;
     cyclic_shift(tmp);
     while(tmp != s){
      cyclic_shift(tmp);
      cnt++;
     }
     ans = lcm(ans, cnt);
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