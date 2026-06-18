#include <bits/stdc++.h>
using namespace std;

#define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl '\n'

int main()
{
    fastIO;
    int n;
    cin >> n;
    if ((n - 3) % 4 == 0)
    {
        cout << "YES" << endl;
        cout << n / 2 + 1 << endl;
        cout << 1 << " " << 2 << " ";
        int i = 4;
        while (i <= n)
        {
            cout << i << " ";
            if (i % 2 == 0)
                i += 3;
            else
                i += 1;
        }
        cout << endl;
        cout << n / 2 << "\n3 ";
        i = 5;
        while (i < n)
        {
            cout << i << " ";
            if (i % 2 == 0)
                i += 3;
            else
                i += 1;
        }
        cout << endl;
    }
    else if (n % 4 == 0)
    {
        cout << "YES" << endl;
        cout << n / 2 << endl;
        int i = 1;
        while (i <= n)
        {
            cout << i << " ";
            if (i % 2 == 0)
                i += 1;
            else
                i += 3;
        }
        cout << endl;
        cout << n / 2 << endl;
        i = 2;
        while (i <= n)
        {
            cout << i << " ";
            if (i % 2 == 0)
                i += 1;
            else
                i += 3;
        }
        cout << endl;
    }
    else
        cout << "NO" << endl;
}