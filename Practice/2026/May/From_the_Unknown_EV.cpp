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

const int mx = 1e5;

void solve()
{
    int line;
    cout << "? " << mx << " ";
    for(int i = 0; i < mx; i++)
        cout << 1 << " \n"[i == mx - 1];
    cout.flush();
    cin >> line;
    int mn_val = mx, l = 1, r = mx;
    while(l <= r){
        int mid = (l + r) / 2;
        int b = (mx + mid - 1) / mid;
        if(b <= line){
            if(b == line)
                mn_val = min(mn_val, mid);
            r = mid - 1;
        }else{
            l = mid + 1;
        }
    }
    int mx_val = -1; l = 1, r = mx;
    while(l <= r){
        int mid = (l + r) / 2;
        int b = (mx + mid - 1) / mid;
        if(b >= line){
            if(b == line)
                mx_val = max(mx_val, mid);
            l = mid + 1;
        }else{
            r = mid - 1;
        }
    }
    if(mn_val == mx_val){
        cout << "! " << mn_val << endl;
        return;
    }
    vector<int> last_query;
    for(int i = mn_val + 1; i <= mx_val; i++){
        last_query.push_back(mn_val);
        last_query.push_back(i - mn_val);
    }
    cout << "? " << sz(last_query);
    for(auto &x: last_query){
        cout << " " << x;
    }
    cout << endl;
    cin >> line;
    reverse(all(last_query));
    int len = mn_val;
    while(line < sz(last_query)){
        int tmp = 0;
        tmp += last_query.back();
        last_query.pop_back();
        tmp += last_query.back();
        last_query.pop_back();
        line--;
        len = tmp;
    }
    cout << "! " << len << endl;
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