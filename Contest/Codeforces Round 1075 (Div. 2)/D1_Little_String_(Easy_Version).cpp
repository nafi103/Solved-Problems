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
 const int N = 2e5 + 10;
int fact[N];
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
    for(int i = 0; i < n - 1; i++){
        if(str[i] == '1'){
            ans = (ans * 2) % mod;
            c = c / gcd(c, 2);
        }else{
            ans = (ans * i) % mod;
            c = c / gcd(c, i);
        }
    }
    if(c == 1){
        cout << -1 << endl;
    }else{
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
     fact[0] = 1;
    for(int i = 1; i < N; i++)
        fact[i] = (fact[i - 1] * i) % mod;
     cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}