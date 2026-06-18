#include <bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        char mxrc = 0,mxbc= 0,rc = 0,bc=0;
        char arr[8][8];
        for (int i = 0; i < 8; i++)
        {
            for (int j = 0; j < 8; j++)
            {
                cin>>arr[i][j];
            }
        }
        for (int i = 0; i < 8; i++)
        {
            for (int j = 0; j < 8; j++)
            {
                if(arr[i][j]=='R')  rc++;
            }
            if(rc>mxrc) mxrc=rc;
            rc =0;
        }
        for (int i = 0; i < 8; i++)
        {
            for (int j = 0; j < 8; j++)
            {
                if(arr[j][i]=='B')  bc++;
            }
            if(bc>mxbc) mxbc=bc;
            bc=0;
        }
        if(mxrc==8) cout<<"R"<<endl;
        else    cout<<"B"<<endl;
    }
}