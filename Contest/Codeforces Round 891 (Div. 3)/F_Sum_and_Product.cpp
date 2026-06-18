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
    int n, b, c;
    cin >> n;
    map<int,int> cnt;
    for(int i = 0, x; i < n; i++){
        cin >> x;
        cnt[x]++;
    }
    cin >> n;
    while(n--){
        cin >> b >> c;
        int d = b * b - 4 * c, rd = sqrt(d);
        if(d < 0 or rd * rd != d or (b - d) % 2 != 0){
            cout << 0 << " ";
            continue;
        }
        if(d == 0){
            int x = b / 2;
            if(cnt.count(x) == 0)
                cout << 0 << " ";
            else{
                c = cnt[x];
                cout << (c * (c - 1)) / 2 << " ";
            }
        }else{
            int x1 = (b + rd) / 2, x2 = (b - rd) / 2;
            if(cnt.count(x1) == 0 or cnt.count(x2) == 0){
                cout << 0 << " ";
            }else{
                cout << cnt[x1] * cnt[x2] << " ";
            }
        }
    }
    cout << endl;
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