#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int N = 1e6 + 1;
int phi[N];
long long pre[N];

void phi_1_to_n(int n) {
    for (int i = 0; i <= n; i++)
        phi[i] = i;

    for (int i = 2; i <= n; i++) {
        if (phi[i] == i) {
            for (int j = i; j <= n; j += i)
                phi[j] -= phi[j] / i;
        }
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);

    phi_1_to_n(N - 1);
    for(int i = 1; i < N; i++){
        for(int j = i + i; j < N; j += i){
            pre[j] += phi[j / i] * 1ll * i;
        }
    }
    for(int i = 1; i < N; i++){
        pre[i] += pre[i - 1];
    }

    int n;
    while(cin >> n and n){
        cout << pre[n] << endl;
    }
}