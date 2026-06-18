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
 int fact[21];
 void solve()
{
    int n;
    cin >> n;
    int m = log2(n) + 1;
    vector<pair<int, string>> bit(m);
    for(auto &[cnt, str]: bit){
        cin >> str;
        cnt = count(all(str), '1');
    }
     sort(all(bit), [&](pair<int, string> &a, pair<int, string> &b){
        return a.first > b.first;
    });
     vector<int> p(n, 0);
    for(int i = 0; i < m; i++){
        auto &[val, str] = bit[i];
        for(int j = 0; j < n; j++){
            if(str[j] == '1')
                p[j] += (1 << i);
        }
    }
     sort(all(p));
    for(int i = 0; i < n; i++){
        if(p[i] != i + 1){
            cout << 0 << endl;
            return;
        }
    }
     int cnt = 1, ans = 1;
    for(int i = 1; i < m; i++){
        if(bit[i].first != bit[i - 1].first){
            ans *= fact[cnt];
            cnt = 1;
        }else{
            cnt++;
        }
    }
     ans *= fact[cnt];
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
     fact[0] = 1;
    for(int i = 1; i < 21; i++){
        fact[i] = fact[i - 1] * i;
    }
     cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}