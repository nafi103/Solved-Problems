#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 int query(int i, int j){
    cout << "? " << i << " " << j << endl;
    cin >> i;
    return i;
}
 void solve()
{
    int n, tmp;
    cin >> n;
    for(int i = 1; i <= 2 * n - 2; i += 2){
        int j = i + 1;
        int q = query(i, j);
        if(q){
            cout << "! " << i << endl;
            return;
        }
    }
    tmp = query(1, 2 * n - 1);
    if(tmp){
        cout << "! " << 1 << endl;
        return;
    }
    tmp = query(2, 2 * n - 1);
    if(tmp){
        cout << "! " << 2 << endl;
        return;
    }
    cout << "! "<< 2 * n << endl;
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