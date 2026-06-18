#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
#define set_bits(x) __builtin_popcountll(x)
#define LSOne(x) ((x) & (-x))
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 bool correct(int a, int b){
    while(a > 0 and b > 0){
        int x = LSOne(a), y = LSOne(b);
        if(x > y)
            return false;
        a -= x;
        b -= y;
    }
    return true;
}
 void solve()
{
    int a, b;
    cin >> a >> b;
    if(a > b or set_bits(a) < set_bits(b) or !correct(a, b)){
        cout << "NO" << endl;
        return;
    }
    cout << "YES" << endl;
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