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

vector<int> get_primes(int n){
    vector<int> primes;
    for(int i = 2; i * i < n; i++){
        if(n % i == 0){
            primes.push_back(i);
            while(n % i == 0)
                n /= i;
        }
    }
    if(n > 1)
        primes.push_back(n);
    return primes;
}

int calc(int n, vector<int> &primes, int &len){
    int bad = 0, r = (1 << len);
    for(int i = 1; i < r; i++){
        int l = 1, cnt = 0;
        for(int j = 0; j < len; j++){
            if(i & (1 << j)){
                cnt++;
                l = lcm(l, primes[j]);
            }
        }
        if(cnt & 1)
            bad += n / l;
        else
            bad -= n / l;
    }
    return bad;
}

void solve()
{
    int a, b, n;
    cin >> a >> b >> n;
    vector<int> primes = get_primes(n);
    int len = sz(primes);
    int not_coprime_a = calc(a - 1, primes, len), not_coprime_b = calc(b, primes, len);
    cout << b - a + 1 - (not_coprime_b - not_coprime_a) << endl;
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
        cout<<"Case #"<<z<<": ";
        solve();
    }
}