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
    string str;
    cin >> str;
    int n = sz(str), opening = n / 2, closing = n / 2;
    vector<bool> unknown(n, false);
    vector<int> pref(n);
    for(int i = 0; i < n; i++){
     char &c = str[i];
     if(c == '(')
      opening--;
     else if(c == ')')
      closing--;
     else
      unknown[i] = true;
    }
    if(opening == 0 or closing == 0){
     cout << "YES" << endl;
     return;
    }
    int opening_last = -1, closing_first = inf;
    for(int i = 0; i < n; i++){
     if(str[i] == '?'){
      if(opening){
       str[i] = '(';
       opening--;
       opening_last = i;
      }else{
       str[i] = ')';
       closing--;
       closing_first = min(closing_first, i);
      }
     }
    }
    swap(str[opening_last], str[closing_first]);
    for(int i = 0; i < n; i++){
     pref[i] = (str[i] == '(' ? 1 : -1);
     if(i)
      pref[i] += pref[i - 1];
     if(pref[i] == -1){
      cout << "YES" << endl;
      return;
     }
    }
    cout << "NO" << endl;
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