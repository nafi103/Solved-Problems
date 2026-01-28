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
    int n, mn_pos, sum;
    cin >> n;
    vector<int> a(n);
    for(int i = 0; i < n; i++)
        cin >> a[i];
    mn_pos = (min_element(all(a)) - a.begin()) + 1;
    sum = accumulate(all(a), 0ll);
    if(sum & 1){
        cout << 0 << endl;
        return;
    }
    bitset<200005> b;
    b[0] = 1;
    for(auto &x: a){
        b |= (b << x);
    }
    if(b[sum / 2]){
        cout << 1 << endl;
        for(int i = 0; i < n; i++){
            if((a[i] & 1) or b[(sum - a[i]) / 2] == 0){
                cout << i + 1 << endl;
                break;
            }
        }
    }else{
        cout << 0 << endl;
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
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}