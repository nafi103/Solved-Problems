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
 const int N = 2e5 + 10;
int n, a[N];
 void input(){
    cin >> n;
    for (int i = 0; i < n; i++)
        cin >> a[i];
}
 void solve()
{
    input();
    int ans = 0;
    for (int i = 0; i < n; i++){
        int r = min(a[i], (n - i - 1) / a[i]);
        for (int j = 1; j <= r; j++)
        {
            int p = i + j * a[i];
            if(a[p] == j)
                ans++;
        }
        r = min(a[i] - 1, i / a[i]);
        for (int j = 1; j <= r; j++){
            int p = i - j * a[i];
            if(a[p] * a[i] == i - p)
                ans++;
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