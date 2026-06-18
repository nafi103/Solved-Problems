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
 pair<int,bool> f(int ini, int x, int y){
    bool flag = false;
    while (x > 0 and (ini/y) > 0){
        if(ini % y == 0)
            flag = true;
        int rem = ini % y, rmv = ini / y;
        int iteration = min(rem / rmv, x);
        x -= iteration;
        ini -= iteration * rmv;
        if(x >= 1){
            if(ini % y == 0)
                flag = true;
            ini -= ini / y;
            x--;
        }
    }
    return make_pair(ini, flag);
}
 bool not_possible(int x, int y, int k){
    auto [final, flag] = f(1e12, x, y);
    return final < k;
}
 void solve()
{
    int x, y, k;
    cin >> x >> y >> k;
    if(k < y){
        cout << k << endl;
        return;
    }
    if(not_possible(x, y, k)){
        cout << -1 << endl;
        return;
    }
    int l = k, r = 1e12;
    while(l <= r){
        int mid = (l + r) / 2;
        auto [final, flag] = f(mid, x, y);
        if(final == k and !flag){
            cout << mid << endl;
            return;
        }
        if(final > k or (final == k and flag)){
            r = mid - 1;
        }else{
            l = mid + 1;
        }
    }
    cout << -1 << endl;
}
 void solve2()
{
    int x, y, k;
    cin >> x >> y >> k;
    if(y == 1){
        cout << -1 << endl;
        return;
    }
    for (int i = 0; i < x; )
    {
        int cur = (k - 1) / (y - 1);
        if (cur == 0)
        {
            break;
        }
        int fk = (cur + 1) * (y - 1) + 1;
        int cnt = (fk - k + cur - 1) / cur;
        cnt = min(x - i, cnt);
        k += cnt * cur;
        if (k > 1e12)
        {
            cout << -1 << '\n';
            return;
        }
        i += cnt;
    }
    cout << k << endl;
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
        solve2();
    }
}