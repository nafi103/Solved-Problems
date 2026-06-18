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
using Int = __int128;

void print_int128(__int128 n) {
    if (n == 0) {
        cout << "0\n";
        return;
    }
    
    string s;
    bool is_negative = false;
    
    if (n < 0) {
        is_negative = true;
    }

    while (n != 0) {
        int digit = n % 10;
        s += to_string(abs(digit));
        n /= 10;
    }

    if (is_negative) {
        s += '-';
    }

    reverse(s.begin(), s.end());
    cout << s << "\n";
}

bool check(vector<int> &arr, Int target, int &k, int &n){
    Int op = 0;
    for(int i = 0; i < n; i++){
        int &x = arr[i];
        if((Int)x >= target)
            continue;
        Int need = (target - x + i) / (i + 1);
        op += need;
        if(need > (Int)k or op > (Int)k)
            return false;
    }
    return true;
}

void solve()
{
    int n, k;
    cin >> n >> k;
    vector<int> arr(n);
    for(int i = 0; i < n; i++)
        cin >> arr[i];

    Int l = 1, r = 1;
    for(int i = 0; i < 38; i++)
        r *= 10;
    while(l <= r){
        Int mid = (l + r) / 2;
        if(check(arr, mid, k, n))
            l = mid + 1;
        else
            r = mid - 1;
    }
    print_int128(r);
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}