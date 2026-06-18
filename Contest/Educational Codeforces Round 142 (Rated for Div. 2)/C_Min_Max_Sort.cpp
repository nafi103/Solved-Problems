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
    int n;
    cin >> n;
    vector<int> id(n + 1);
    for(int i = 1, x; i <= n; i++){
        cin >> x;
        id[x] = i;
    }
     int m1 = (n + 1) / 2, m2 = (n + 2) / 2;
    while(m1 >= 1){
        if(m1 < m2){
            int nxt = m1 + 1, prev = m2 - 1;
            if(id[m1] > id[nxt] or id[m2] < id[prev]){
                cout << m1 << endl;
                return;
            }
        }
        m1--, m2++;
    }
     cout << 0 << endl;
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