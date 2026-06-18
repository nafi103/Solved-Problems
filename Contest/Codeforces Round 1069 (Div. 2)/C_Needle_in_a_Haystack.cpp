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
 const int N = 26;
vector<int> s(N), t(N);
 void solve()
{
    for(int i = 0; i < N; i++){
     s[i] = t[i] = 0;
    }
    string a, b, ans = "";
    cin >> a >> b;
    for(auto &c: a){
     s[c - 'a']++;
    }
    for(auto &c: b){
     t[c - 'a']++;
    }
    for(int i = 0; i < N; i++){
     if(t[i] < s[i]){
      cout << "Impossible" << endl;
      return;
     }
    }
    a.push_back('$');
    int n = sz(b);
    for(int i = 0, p = 0; i < n; i++){
     for(auto [j, c] = pair{0, 'a'}; j < N; j++, c++){
      if(t[j] > s[j]){
       ans.push_back(c);
       t[j]--;
       if(a[p] == c){
        p++;
        s[j]--;
       }
       break;
      }else if(a[p] == c){
       ans.push_back(c);
       p++;
       s[j]--;
       t[j]--;
       break;
      }
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