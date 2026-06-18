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
 const int N = 5e5 + 10;
int n, q, a[N], b[32], c, ans;
 void input(){
    cin >> n >> q;
    for(int i = 0; i < n; i++){
        cin >> a[i];
    }
    sort(a, a + n, greater<int>());
    n = (n > 30 ? 31 : n);
}
 void solve()
{
    input();
    while(q--){
        for(int i = 0; i < n; i++)
            b[i] = a[i];
        cin >> c;
        ans = 0;
        for(int i = 29; i >= 0; i--){
            int tmp = 0;
            for(int j = 0; j < n; j++){
                tmp += ((a[j] >> i) & 1);
            }
            if(tmp > ((c >> i) & 1))
                break;
            if(tmp < ((c >> i) & 1)){
                int pos = 0;
                for(int j = 1; j < n; j++){
                    if((a[j] & ((1 << i) - 1)) > (a[pos] & ((1 << i) - 1)))
                        pos = j;
                }
                ans += (1 << i) - (a[pos] & ((1 << i) - 1));
                a[pos] += (1 << i) - (a[pos] & ((1 << i) - 1));
            }
        }
        cout << ans << endl;
        for(int i = 0; i < n; i++)
            a[i] = b[i];
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}