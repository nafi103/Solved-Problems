#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
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
    int n, c, ans = 1;
    cin >> n >> c;
    string str;
    cin >> str;
    if(str[0] == '0' or str.back() == '0'){
        cout << -1 << endl;
        return;
    }
    vector<int> remaining;
    str[0] = str[n - 1] = '1';
    debug(str)
    for(int i = 0; i < n - 1; i++){
        if(str[i] == '1' or (str[i] == '?' and i % 2 == 0)){
            ans = (ans * 2) % mod;
            c = c / gcd(c, 2);
        }else if(str[i] == '0' or (str[i] == '?' and i == 1)){
            ans = (ans * i) % mod;
            c = c / gcd(c, i);
        }else{
            remaining.push_back(i);
        }
    }
    if(c == 1){
        cout << -1 << endl;
        return;
    }
    if(__builtin_popcount(c) != 1 or remaining.empty()){
        int m = sz(remaining);
        for(int i = 0; i < m; i++){
            ans = (ans * 2) % mod;
        }
        cout << ans << endl;
        return;
    }else{
        int max_two = __builtin_ctz(c) - 1;
        while(max_two and !remaining.empty()){
            ans = (ans * 2) % mod;
            c /= 2;
            remaining.pop_back();
            max_two--;
        }
        for(auto &x: remaining){
            ans = (ans * x) % mod;
        }
        cout << ans << endl;
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
        debug(z)
        // cout<<"Case "<<z<<": ";
        solve();
    }
}